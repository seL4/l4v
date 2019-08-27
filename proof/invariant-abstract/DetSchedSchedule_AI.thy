(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DetSchedSchedule_AI
imports "$L4V_ARCH/ArchDetSchedDomainTime_AI"
begin

context begin interpretation Arch .

requalify_facts
  kernelWCET_us_non_zero
  kernelWCET_ticks_non_zero

end

lemma do_machine_op_cur_sc_chargeable[wp]:
  "do_machine_op f \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding do_machine_op_def by wpsimp

lemma as_user_cur_sc_chargeable[wp]:
  "as_user f d \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding as_user_def cur_sc_chargeable_def2
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_at_pred_def dest!: get_tcb_SomeD)
  apply (case_tac "cur_thread s = f"; simp)
  apply fastforce
  by fastforce

definition
  refill_list_sum :: "refill list \<Rightarrow> nat"
where
  "refill_list_sum l = sum_list (map (unat \<circ> r_amount) l)"

lemma refill_list_sum_hd_middle_last:
  "refill_list_sum (a # b @ [c]) = ( unat (r_amount a) +
    (sum_list (map (unat \<circ> r_amount) b) + unat (r_amount c)))"
  unfolding refill_list_sum_def
  by clarsimp

lemma rt_assumptions:
  "valid_refills t k s \<Longrightarrow>
       (\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) t s \<longrightarrow>
                   (refill_list_sum (sc_refills sc) \<le> unat k)) s "
  "valid_refills scp k s \<Longrightarrow> MIN_BUDGET \<le> k"
  sorry (* Assumption pending an update *)

lemmas budgets_bounded_above = rt_assumptions(1)
lemmas budgets_bounded_below = rt_assumptions(2)

lemma valid_machine_time_detype[simp]:
  "valid_machine_time (detype S s) = valid_machine_time s"
  by (clarsimp simp: valid_machine_time_def detype_def)

lemma cur_time_no_overflow:
  "valid_machine_time s \<Longrightarrow> cur_time s \<le> cur_time s + kernelWCET_ticks"
  apply (rule no_plus_overflow_neg)
  apply (rule minus_one_helper5)
   using kernelWCET_ticks_non_zero apply simp
  apply (erule cur_time_bounded)
  done

lemma refill_ready_wp:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (r_time (refill_hd sc) \<le> cur_time s + kernelWCET_ticks) s\<rbrace>
   refill_ready scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: refill_ready_def)

lemma is_round_robin_wp:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow> Q (sc_period sc = sc_budget sc) s\<rbrace>
    is_round_robin scp
   \<lbrace>Q\<rbrace>" by (wpsimp simp: is_round_robin_def)

lemma refill_sufficient_wp:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (MIN_BUDGET
               \<le> (if r_amount (refill_hd sc) < usage then 0
                   else r_amount (refill_hd sc) - usage)) s\<rbrace>
   refill_sufficient scp usage
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: refill_sufficient_def get_refills_def sufficient_refills_defs
       split_del: if_split)

lemma refill_full_wp:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (length (sc_refills sc) = sc_refill_max sc) s\<rbrace>
   refill_full scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: refill_full_def)

(* FIXME: move *)
lemma update_sk_obj_ref_lift:
  "(\<And>sc. \<lbrace>P\<rbrace> set_simple_ko C ref (f (K new) sc) \<lbrace>\<lambda>rv. P\<rbrace>) \<Longrightarrow>
   \<lbrace>P\<rbrace> update_sk_obj_ref C f ref new \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def get_simple_ko_wp | assumption)+
  done

(* FIXME: move *)
lemma invs_cur_sc_tcb [elim!]:
  "invs s \<Longrightarrow> cur_sc_tcb s"
  by (clarsimp simp: invs_def)

(* This rule can cause problems with the simplifier if rule unification chooses a Q that does not
   specify proj. If necessary, this can be worked around by manually specifying proj. *)
lemma update_sched_context_sc_at_pred_n_indep:
  "(\<And>sc. P (proj (f sc)) = P (proj sc)) \<Longrightarrow>
   update_sched_context csc_ptr f \<lbrace>\<lambda>s. Q (sc_at_pred_n N proj P sc_ptr s)\<rbrace>"
  by (wpsimp wp: update_sched_context_wp simp: sc_at_pred_n_def obj_at_def)

lemma tcb_sched_action_lift:
  "(\<And>f s. P s \<Longrightarrow> P (ready_queues_update f s))
  \<Longrightarrow> \<lbrace>P\<rbrace> tcb_sched_action a b \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def etcb_at_def thread_get_def)

lemma tcb_sched_enqueue_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and active_sc_tcb_at thread
     and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  by (clarsimp simp: valid_ready_qs_def tcb_sched_enqueue_def obj_at_def etcb_defs)

lemma tcb_sched_enqueue_wp:
  "\<lbrace>st_tcb_at runnable thread and active_sc_tcb_at thread
             and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. in_ready_q thread::det_state \<Rightarrow> bool\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def thread_get_def)
     (fastforce simp: in_queue_2_def tcb_sched_enqueue_def obj_at_def)

lemma tcb_sched_append_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and active_sc_tcb_at thread
     and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  by (clarsimp simp: valid_ready_qs_def tcb_sched_append_def obj_at_def etcb_defs)

lemma tcb_sched_append_wp:
  "\<lbrace>st_tcb_at runnable thread and active_sc_tcb_at thread
             and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. in_ready_q thread::det_state \<Rightarrow> bool\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def thread_get_def)
     (fastforce simp: in_queue_2_def tcb_sched_append_def obj_at_def)

(* this is not safe! *)
(* if in_ready_q thread then this will break valid_blocked  *)
lemma tcb_sched_dequeue_valid_ready_qs:
  "\<lbrace>valid_ready_qs\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: valid_ready_qs_def2 etcb_at_def tcb_sched_dequeue_def
         split: option.splits)
  apply blast
  done

lemma tcb_sched_dequeue_valid_ready_qs':
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) thread s \<longrightarrow>
      valid_ready_qs_2
             (\<lambda>a b. if a = tcb_domain tcb \<and> b = tcb_priority tcb then tcb_sched_dequeue thread (ready_queues s (tcb_domain tcb) (tcb_priority tcb)) else ready_queues s a b) (cur_time s)
             (kheap s)\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (subgoal_tac "tcb = tcba")
  apply (clarsimp simp: valid_ready_qs_def2 etcb_at_def tcb_sched_dequeue_def
         split: option.splits)
  apply (clarsimp simp: obj_at_def)
  done

crunches tcb_sched_action
for valid_release_q[wp]: valid_release_q
and release_queue[wp]: "\<lambda>s. P (release_queue s)"

lemma tcb_sched_enqueue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_enqueue_def not_queued_def
         split: option.splits)
  done

lemma tcb_sched_append_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_append_def not_queued_def
                  split: option.splits)
  done

lemma tcb_sched_dequeue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (fastforce simp: ct_not_in_q_def etcb_at_def tcb_sched_dequeue_def
                         not_queued_def
                   split: option.splits)
  done

crunches tcb_sched_action,tcb_release_remove
for is_activatable[wp]: "is_activatable t"
and is_activatable_ct[wp]: "\<lambda>s. is_activatable (cur_thread s) s"
and ct_in_cur_domain[wp]: ct_in_cur_domain
and switch_in_cur_domain[wp]: switch_in_cur_domain

crunch weak_valid_sched_action[wp]: tcb_sched_action "weak_valid_sched_action"

lemma test_sc_refill_max_release_queue_update'[simp]:
  "test_sc_refill_max t (release_queue_update f s) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_release_queue_update'[simp]:
  "active_sc_tcb_at t (release_queue_update f s) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma tcb_release_remove_rq_reprogram_timer[wp]:
  "\<lbrace>(\<lambda>s. P (filter (\<lambda>x. x \<noteq> thread) (release_queue s)) (reprogram_timer s))\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_ s. P (release_queue s) (reprogram_timer s)\<rbrace>"
  unfolding tcb_release_remove_def
  by (wpsimp simp: tcb_sched_dequeue_def)

lemma tcb_release_remove_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp simp: active_sc_tcb_at_defs tcb_release_remove_def weak_valid_sched_action_def
               tcb_sched_dequeue_def refill_prop_defs)
   (clarsimp split: option.splits kernel_object.splits)

lemma tcb_release_remove_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def)

crunch valid_sched_action[wp]: tcb_sched_action valid_sched_action

(* valid_blocked_except_set doesn't say much; S can contain anything that is not blocked*)
(* see also valid_blocked_except_set_subset *)
(* use in conjunction with valid_sched_except_blocked *)
lemma valid_blocked_except_set_less:
  "\<lbrakk>valid_blocked_except_set (insert t S) s;
          in_ready_q t s \<or> in_release_q t s
          \<or> scheduler_action s = switch_thread t \<or> cur_thread s = t
          \<or>  \<not> st_tcb_at runnable t s \<or> \<not> active_sc_tcb_at t s\<rbrakk>
       \<Longrightarrow> valid_blocked_except_set S s"
  by (clarsimp simp: valid_blocked_except_set_def not_queued_def not_in_release_q_def
                      in_queue_2_def)
     (case_tac st; fastforce simp: runnable_eq_active active_sc_tcb_at_defs split: option.splits)

lemma tcb_sched_enqueue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace> \<comment> \<open>not_queued thread \<longrightarrow> in_ready_q thread\<close>
    tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_enqueue_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_enqueue_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_enqueue_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemmas tcb_sched_enqueue_valid_blocked_enqueue =
  tcb_sched_enqueue_valid_blocked_except_set

(* the same as the case of tcb_sched_enqueue *)
lemma tcb_sched_append_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace> \<comment> \<open>not_queued thread \<longrightarrow> in_ready_q thread\<close>
    tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_append_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_append_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_append_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_append_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: thread_get_def tcb_sched_action_def)

lemma tcb_sched_enqueue_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: thread_get_def tcb_sched_action_def)

(* tcb_sched_dequeue *)
lemma tcb_sched_dequeue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set (insert thread S)\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  by (fastforce simp: tcb_sched_dequeue_def pred_tcb_at_def
                      valid_blocked_except_def not_queued_def obj_at_def)

lemma tcb_sched_dequeue_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. thread \<in> S \<or> scheduler_action s = switch_thread thread
           \<or> in_release_q thread s \<or> thread = cur_thread s
           \<or> \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s)) \<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  apply (clarsimp simp: valid_blocked_except_def in_queue_2_def not_queued_def not_in_release_q_def
                  tcb_sched_dequeue_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp)
  by (case_tac "t=thread"; fastforce simp: pred_tcb_at_def obj_at_def)

lemma tcb_sched_dequeue_valid_blocked_except_set_remove: (* valid_sched is broken at thread *)
  "\<lbrace>valid_blocked_except_set (insert thread S) and
             (\<lambda>s. scheduler_action s = switch_thread thread
                  \<or> in_release_q thread s \<or> thread = cur_thread s
                  \<or> \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s)) \<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  apply (clarsimp simp: valid_blocked_except_def not_queued_def in_queue_2_def not_in_release_q_def
                        tcb_sched_dequeue_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp)
  by (case_tac "t=thread"; fastforce simp: pred_tcb_at_def obj_at_def)

lemma tcb_sched_dequeue_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def)

lemma tcb_sched_enqueue_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread
    and not_cur_thread thread
    and active_sc_tcb_at thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: tcb_sched_enqueue_valid_blocked_enqueue)

lemma tcb_sched_enqueue_valid_sched_weak:
  "\<lbrace>valid_sched and st_tcb_at runnable thread
    and not_cur_thread thread
    and active_sc_tcb_at thread
    and budget_ready thread and budget_sufficient thread\<rbrace>
   tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp,
      fastforce simp: valid_sched_def elim: valid_blocked_except_set_weaken)

lemma tcb_sched_append_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and active_sc_tcb_at thread
     and not_cur_thread thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread\<rbrace>
      tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: tcb_sched_append_valid_blocked_except_set)

(* Move *)
lemma if_fun_simp2: "(\<lambda>x1 x2. if x1 = y1 \<and> x2 = y2 then f y1 y2 else f x1 x2) = f "
  by (rule all_ext) auto

lemma tcb_sched_dequeue_not_queued_inv:
  "\<lbrace>P and not_queued thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp simp: tcb_sched_dequeue_def tcb_sched_action_def)
  apply (clarsimp simp: not_queued_def obj_at_def elim!: rsubst[where P=P])
  by (drule_tac x="tcb_domain tcb" and y="tcb_priority tcb" in spec2)
     (subst filter_True; clarsimp simp: if_fun_simp2)

lemma tcb_sched_dequeue_valid_sched_not_queued:
  "\<lbrace>valid_sched and not_queued thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: tcb_sched_dequeue_not_queued_inv)

lemma tcb_sched_dequeue_valid_sched_except_blocked: (* in_ready_q thread *)
  "\<lbrace>valid_sched\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: tcb_sched_dequeue_valid_blocked_except_set
                   tcb_sched_dequeue_valid_ready_qs)+

(* tcb_release_remove *)
lemma tcb_release_remove_valid_blocked_except_set_if: (* is this usable? *)
  "\<lbrace>\<lambda>s. if not_in_release_q tcb_ptr s then valid_blocked_except_set {tcb_ptr} s else valid_blocked s\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except_set {tcb_ptr} s\<rbrace>"
  unfolding tcb_release_remove_def
  apply (wpsimp)
  apply (clarsimp simp: valid_blocked_except_set_def tcb_sched_dequeue_def obj_at_def split: if_splits)
   apply (drule_tac x=t in spec; clarsimp )
   apply (case_tac "not_in_release_q t s"; clarsimp)
   apply (clarsimp simp: not_in_release_q_def in_release_queue_def not_in_release_q_2_def)
  apply (clarsimp simp: not_in_release_q_2_def in_queue_2_def)
  apply (drule_tac x=t in spec; clarsimp simp: not_in_release_q_def)
  done

lemma tcb_release_remove_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except_set (insert tcb_ptr S) s\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  by (fastforce simp: tcb_sched_dequeue_def pred_tcb_at_def valid_blocked_def
                      valid_blocked_except_def not_in_release_q_def obj_at_def)

lemma tcb_release_remove_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. thread \<in> S \<or> scheduler_action s = switch_thread thread
                \<or> in_ready_q thread s \<or> thread = cur_thread s
                \<or> \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s)) \<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  apply (clarsimp simp: valid_blocked_except_def not_queued_def in_queue_2_def not_in_release_q_def
                        tcb_sched_dequeue_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp)
  by (case_tac "t=thread"; fastforce simp: pred_tcb_at_def obj_at_def)

lemma tcb_release_remove_valid_blocked_except_set_remove: (* valid_sched is broken at thread *)
  "\<lbrace>valid_blocked_except_set (insert thread S) and
             (\<lambda>s. scheduler_action s = switch_thread thread
                  \<or> in_ready_q thread s \<or> thread = cur_thread s
                  \<or> \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s)) \<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  apply (clarsimp simp: valid_blocked_except_def not_queued_def in_queue_2_def not_in_release_q_def
                        tcb_sched_dequeue_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp)
  by (case_tac "t=thread"; fastforce simp: pred_tcb_at_def obj_at_def)

lemmas tcb_release_remove_valid_blocked =
  tcb_release_remove_valid_blocked_except_set

lemmas tcb_release_remove_valid_blocked_const =
  tcb_release_remove_valid_blocked_except_set_const

lemmas tcb_release_remove_valid_blocked_remove =
  tcb_release_remove_valid_blocked_except_set_remove


(* set_scheduler_action *)
crunches set_scheduler_action
for valid_ready_qs[wp]: "valid_ready_qs"
and valid_release_q[wp]: "valid_release_q"

crunches tcb_release_remove
for valid_ready_qs[wp]: "valid_ready_qs"

lemma set_scheduler_action_rct_ct_not_in_q[wp]:
  "\<lbrace>ct_not_queued\<rbrace> set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (fastforce simp: ct_not_in_q_def not_queued_def)
  done

lemma set_scheduler_action_rct_is_activatable[wp]:
  "\<lbrace>st_tcb_at activatable t\<rbrace>
     set_scheduler_action resume_cur_thread
   \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_rct_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: weak_valid_sched_action_def)
  done

lemma set_scheduler_action_wp:
  "\<lbrace>\<lambda>s. Q (scheduler_action_update (\<lambda>_. a) s)\<rbrace> set_scheduler_action a \<lbrace>\<lambda>_.Q\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  done

lemma set_scheduler_action_rct_valid_sched_action[wp]:
  "\<lbrace>\<lambda>s. st_tcb_at activatable (cur_thread s) s\<rbrace>
     set_scheduler_action resume_cur_thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def  | wp set_scheduler_action_wp)+
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_rct_ct_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s\<rbrace>
     set_scheduler_action resume_cur_thread  \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: valid_sched_action_def  | wp set_scheduler_action_wp)+
  apply (clarsimp simp: in_cur_domain_def ct_in_cur_domain_2_def)
  done

lemma set_scheduler_action_valid_blocked_simple:
  "\<lbrace>valid_blocked_except_set S and simple_sched_action and (K $ (simple_sched_action_2 schact)) \<rbrace>
   set_scheduler_action schact
   \<lbrace>\<lambda>_. (valid_blocked_except_set S)::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  by (simp add: valid_blocked_except_set_def simple_sched_action_def split: scheduler_action.splits)

lemma set_scheduler_action_valid_blocked_except_set: (* when the next one doesn't hold *)
  "\<lbrace>valid_blocked_except_set S and (\<lambda>s. scheduler_action s = switch_thread t) \<rbrace>
     set_scheduler_action act
   \<lbrace>\<lambda>_. valid_blocked_except_set (insert t S)::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_blocked_except_set_def split: scheduler_action.splits
          | wp set_scheduler_action_wp)+ fastforce

lemma set_scheduler_action_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
                t \<in> S \<or> in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
                  \<or> \<not> (st_tcb_at active t s \<and> active_sc_tcb_at t s)) \<rbrace>
     set_scheduler_action act
   \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_blocked_except_set_def split: scheduler_action.splits
          | wp set_scheduler_action_wp)+
     (fastforce simp: in_queue_2_def not_queued_def not_in_release_q_def active_sc_tcb_at_defs
               split: option.splits dest!: get_tcb_SomeD)

lemma set_scheduler_action_valid_blocked_except_set_remove:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert t S) (s\<lparr>scheduler_action := switch_thread t\<rparr>)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)
     (clarsimp simp: valid_blocked_except_def)

lemmas set_scheduler_action_valid_blocked =
  set_scheduler_action_valid_blocked_except_set

lemmas set_scheduler_action_valid_blocked_const =
  set_scheduler_action_valid_blocked_except_set_const

lemmas set_scheduler_action_valid_blocked_remove =
 set_scheduler_action_valid_blocked_except_set_remove

crunch valid_ntfn_q[wp]: set_scheduler_action valid_ntfn_q

lemma set_scheduler_action_rct_valid_sched_simple:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and simple_sched_action\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_scheduler_action_valid_blocked_simple)

lemma set_scheduler_action_rct_valid_sched_ct:
  "\<lbrace>valid_sched and ct_not_queued and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_scheduler_action_valid_blocked_const)

lemma set_scheduler_action_cnt_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: ct_not_in_q_def)
  done

lemma set_scheduler_action_cnt_is_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_cnt_is_activatable'[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>r s. is_activatable (t s) s\<rbrace>"
  apply (wp set_scheduler_action_wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_cnt_switch_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (simp add: set_scheduler_action_def, wp, simp)

lemma set_scheduler_action_cnt_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: ct_in_cur_domain_def)
  done

lemma set_scheduler_action_cnt_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: weak_valid_sched_action_def)
  done

lemma set_scheduler_action_cnt_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def, wp set_scheduler_action_wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_cnt_weak_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def simple_sched_action_def split: scheduler_action.splits
      | wp set_scheduler_action_valid_blocked_const)+

lemma set_scheduler_action_simple_sched_action[wp]:
  "\<lbrace>K $ simple_sched_action_2 action\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (simp add: set_scheduler_action_def | wp)+

lemma set_sched_action_cnt_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (simp add: set_scheduler_action_def | wp | wpc)+
  apply (simp add: not_cur_thread_def)
  done
lemma set_sched_action_st_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action (switch_thread thread) \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (simp add: set_scheduler_action_def | wp | wpc)+
  apply (simp add: not_cur_thread_def)
  done

lemma set_scheduler_action_in_release_queue[wp]:
  "\<lbrace>\<lambda>s. P (in_release_queue t s)\<rbrace> set_scheduler_action sa \<lbrace>\<lambda>_ s. P (in_release_queue t s)\<rbrace>"
  apply (simp add: in_release_queue_def, wp set_scheduler_action_wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_scheduler_action sa  \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def active_sc_tcb_at_def)

lemma tcb_sched_action_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> tcb_sched_action action thread  \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def active_sc_tcb_at_def thread_get_def)

lemma tcb_release_remove_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> tcb_release_remove thread  \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def active_sc_tcb_at_def thread_get_def)

lemma set_scheduler_action_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> set_scheduler_action sa  \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def active_sc_tcb_at_def)

lemma tcb_sched_action_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> tcb_sched_action action thread  \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def active_sc_tcb_at_def thread_get_def)

lemma set_scheduler_action_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_scheduler_action sa  \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def active_sc_tcb_at_def)

lemma tcb_sched_action_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> tcb_sched_action action thread  \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def active_sc_tcb_at_def thread_get_def)

(* reschedule_required *)

lemma reschedule_required_lift:
  assumes A: "\<And>t. \<lbrace>P\<rbrace> tcb_sched_action (tcb_sched_enqueue) t \<lbrace>\<lambda>_. P\<rbrace>"
  assumes B: "\<lbrace>P\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> reschedule_required \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding reschedule_required_def
  by (wpsimp wp: A B is_schedulable_wp simp: thread_get_def)

lemma reschedule_required_valid_ready_qs[wp]:
  "reschedule_required \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: reschedule_required_def is_schedulable_def thread_get_def
                  wp: get_sched_context_wp)
  apply (clarsimp simp: pred_tcb_at_def active_sc_tcb_at_def is_refill_sufficient_def
                        obj_at_def test_sc_refill_max_def is_refill_ready_def
               split: option.splits dest!: get_tcb_SomeD)
  by (fastforce simp: Option.is_none_def)

lemma reschedule_required_valid_release_q'[wp]:
  "reschedule_required \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: reschedule_required_def is_schedulable_def thread_get_def
               wp: get_sched_context_wp)

lemma reschedule_required_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_is_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def reschedule_required_def)
  apply (wpsimp wp: set_scheduler_action_wp)
  done

lemma reschedule_required_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_scheduler_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: reschedule_required_def set_scheduler_action_def scheduler_act_not_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  by (case_tac action; wpsimp)

lemma reschedule_required_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
     reschedule_required
   \<lbrace>\<lambda>rv. valid_blocked_except_set S :: det_state \<Rightarrow> bool\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
   (* resume_cur_thread and choose_new_thread *)
    apply ((wpsimp wp: set_scheduler_action_valid_blocked_except_set_const)+)[2]
   (* switch_thread case *)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rename_tac inq; case_tac inq; clarsimp)
    (* in_release_q *)
   apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
   apply (rule_tac Q="(\<lambda>s. x = False) and
        (valid_blocked_except_set S and (\<lambda>s. scheduler_action s = switch_thread x2) and
         in_release_queue x2)" in hoare_weaken_pre)
    apply (clarsimp simp: when_def)
    apply (wpsimp wp: set_scheduler_action_valid_blocked_except_set_const simp: in_release_queue_in_release_q)
   apply (clarsimp simp: is_schedulable_bool_def split: option.splits)
  apply (clarsimp simp: in_release_queue_in_release_q)
    (* not_in_release_q *)
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (rename_tac sched; case_tac sched; clarsimp simp: bind_assoc assert_opt_def)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (rename_tac sc_opt; case_tac sc_opt; clarsimp)
   apply (wpsimp wp: set_scheduler_action_valid_blocked_except_set_const)
       apply (rule_tac Q="\<lambda>_ s. valid_blocked_except_set S s \<and> scheduler_action s = switch_thread x2 \<and> in_ready_q x2 s"
                     in hoare_strengthen_post[rotated], clarsimp)
       apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const tcb_sched_enqueue_wp)+
   apply (fastforce simp: is_schedulable_bool_def active_sc_tcb_at_defs refill_prop_defs
                   split: option.splits dest!: get_tcb_SomeD)
  apply (wpsimp wp: set_scheduler_action_valid_blocked_except_set_const)
  apply (clarsimp simp: valid_blocked_except_set_def)
  apply (drule_tac x=x2 in spec, clarsimp)
  by (fastforce simp: is_schedulable_bool_def active_sc_tcb_at_defs get_tcb_rev
               split: option.splits)

lemmas reschedule_required_valid_blocked =
  reschedule_required_valid_blocked_except_set

lemma reschedule_required_valid_sched':
  "\<lbrace>valid_release_q and valid_ready_qs and weak_valid_sched_action and valid_blocked and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+

lemma reschedule_required_switch_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. not_cur_thread t\<rbrace>"
  apply (simp add: reschedule_required_def, wp)
  done

lemma reschedule_required_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> reschedule_required \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def thread_get_def wp: hoare_drop_imp)

lemma reschedule_required_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> reschedule_required \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def thread_get_def wp: hoare_drop_imp)

lemma reschedule_required_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> reschedule_required \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def thread_get_def wp: hoare_drop_imp)

(* FIXME move *)
lemma set_nonmember_if_cong: "(a \<notin> set (if P then x else y)) = (if P then a \<notin> set x else a \<notin> set y)"
  by auto

lemma switch_thread_valid_sched_is_schedulable:
  "\<lbrakk>scheduler_action s = switch_thread t; valid_sched s; x = in_release_queue t s\<rbrakk>
      \<Longrightarrow> the (is_schedulable_opt t x s)"
   apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def get_tcb_rev
                split: option.splits)
  by (clarsimp simp: is_schedulable_opt_def active_sc_tcb_at_def pred_tcb_at_def
                        test_sc_refill_max_def in_release_queue_def obj_at_def get_tcb_rev)

lemma reschedule_valid_sched_const:
  "\<lbrace> valid_sched \<rbrace> reschedule_required \<lbrace> \<lambda>rv. valid_sched \<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def tcb_sched_action_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action)
    prefer 3
    apply wpsimp+
   apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_blocked_def)
  apply (rename_tac thread)
  apply (clarsimp simp: bind_assoc)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule_tac Q="K (xa = the (Some True)) and
        (valid_sched and (\<lambda>s. scheduler_action s = switch_thread thread)) and (\<lambda>s. in_release_queue thread s = x)" in hoare_weaken_pre)
   apply (wpsimp simp: thread_get_def)
   apply (clarsimp simp: valid_sched_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_ready_qs_2_def valid_sched_action_2_def tcb_sched_enqueue_def
                          weak_valid_sched_action_2_def etcbs_of'_def is_etcb_at'_def
                          etcb_at_def obj_at_def pred_tcb_at_def
                          is_refill_sufficient_def is_refill_ready_def
                   dest!: ko_at_etcbD get_tcb_SomeD)
   apply (rule conjI)
    apply (clarsimp simp: ct_not_in_q_2_def)
   apply (clarsimp simp: valid_blocked_def not_queued_def tcb_sched_enqueue_def)
   apply fastforce
  apply (simp only: pred_conj_def, elim conjE)
  apply (frule (1) valid_sched_switch_thread_is_schedulable, clarsimp)
  done

lemma reschedule_required_simple_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required  \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wpsimp simp: reschedule_required_def)

lemma tcb_sched_enqueue_not_queued:
  "\<lbrace>not_queued t and K (thread \<noteq> t)\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: get_tcb_queue_wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def
                  split: option.splits)
  done

lemma reschedule_required_not_queued:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (clarsimp simp: reschedule_required_def set_scheduler_action_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc scheduler_act_not_def)
    defer 2
    apply (wpsimp+)[2]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rename_tac thread inq schedulable)
  apply (wpsimp wp: tcb_sched_enqueue_not_queued simp: thread_get_def)
  done

lemma not_in_release_q_sa_update[simp]:
  "not_in_release_q t (s\<lparr>scheduler_action :=sa\<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

lemma not_in_release_q_rdq_update[simp]:
  "not_in_release_q t (s\<lparr>ready_queues :=rdq\<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

crunches reschedule_required
for not_in_release_q[wp]: "\<lambda>s. P (not_in_release_q t s)"
  (wp: crunch_wps)

crunches set_scheduler_action
for ct_not_queued[wp]: "ct_not_queued"
and not_queued[wp]: "not_queued t"
and ct_not_in_release_q[wp]: "ct_not_in_release_q"
  (simp: thread_get_def wp: crunch_wps)

lemma reschedule_required_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (rule hoare_pre)
  apply (rule ct_not_queued_lift; wpsimp wp: reschedule_required_not_queued)
  apply (clarsimp simp: not_queued_def scheduler_act_not_def)
  done

lemma reschedule_required_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def)

lemma test_reschedule_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> test_reschedule t \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: test_reschedule_def)
  apply (wpsimp wp: reschedule_required_valid_sched_action)
  done

(* FIXME move *)
lemma sorted_wrt_filter[intro!]: "sorted_wrt f ls \<Longrightarrow> sorted_wrt f (filter P ls)"
  by (induction ls; simp)

(* FIXME move *)
lemma tcb_ready_time_release_queue_update'[simp]:
  "tcb_ready_time t (release_queue_update qs s) = tcb_ready_time t s"
  by (clarsimp simp: tcb_ready_time_def split: option.splits)

lemma tcb_release_remove_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. sorted_release_q\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def sorted_release_q_def tcb_sched_dequeue_def)

lemma tcb_release_remove_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def valid_release_q_def sorted_release_q_def tcb_sched_dequeue_def)

crunches reschedule_required,test_reschedule
for valid_release_q[wp]: valid_release_q
  (wp: set_scheduler_action_wp crunch_wps)

crunches schedule_tcb,set_thread_state_act
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> bool"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> bool"
  (simp: unless_def is_schedulable_def wp: get_sched_context_wp hoare_vcg_if_lift2)

lemma set_thread_state_runnable_valid_ready_qs:
  "\<lbrace>valid_ready_qs and K (runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> bool\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: get_sched_context_wp hoare_drop_imp
              simp: is_schedulable_def set_object_def)
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
                       refill_sufficient_kh_def refill_ready_kh_def
                       is_refill_sufficient_def is_refill_ready_def
                   split: option.splits dest!: get_tcb_SomeD)

lemma set_thread_state_not_queued_valid_ready_qs:
  "\<lbrace>valid_ready_qs and not_queued thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wp | simp add:  set_object_def)+
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                refill_sufficient_kh_def refill_ready_kh_def etcb_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma set_thread_state_runnable_valid_release_q:
  "\<lbrace>valid_release_q and K (runnable ts)\<rbrace>
    set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> bool\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: get_sched_context_wp hoare_drop_imp
              simp: is_schedulable_def set_object_def)
  by (clarsimp simp: in_release_q_def get_tcb_rev
               dest!: get_tcb_SomeD cong: conj_cong) solve_valid_release_q

lemma set_thread_state_not_queued_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp simp: set_object_def)
  by (clarsimp simp: not_in_release_q_def get_tcb_rev
               dest!: get_tcb_SomeD cong: conj_cong) solve_valid_release_q

lemma schedule_tcb_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> schedule_tcb ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: schedule_tcb_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_act_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state_act ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp gts_wp)+
  done

lemma schedule_tcbactive_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> schedule_tcb ref \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_act_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_thread_state_act ref \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s::det_state. P (active_sc_tcb_at t s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp gts_wp)+
  apply (clarsimp dest!: get_tcb_SomeD elim!: rsubst[where P=P], rule iffI)
  by (fastforce split: option.splits if_splits simp: active_sc_tcb_at_defs get_tcb_rev)+

lemma set_thread_state_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def is_schedulable_def
      split_del: if_split
      wp: set_scheduler_action_wp gts_wp hoare_vcg_if_lift2 get_sched_context_wp)
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def
              dest!: get_tcb_SomeD)
  done

lemma set_thread_state_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def
                wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs, rename_tac scp sc n)
  by (intro conjI impI allI; rule_tac x=scp in exI, clarsimp)

lemma set_thread_state_act_not_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not ref\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def
                wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def st_tcb_at_kh_if_split
                  dest!: get_tcb_SomeD)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs split: option.splits)

lemma set_thread_state_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp set_scheduler_action_wp)
  done

lemma set_thread_state_runnable_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def
        | wp set_thread_state_runnable_weak_valid_sched_action)+
  done

lemma set_thread_state_act_not_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not ref\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def
        | wp set_thread_state_act_not_weak_valid_sched_action)+
  done

lemma set_thread_state_cur_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     set_thread_state ref ts \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp set_scheduler_action_wp)
  done

lemma set_thread_state_etcb_at[wp]: "\<lbrace>etcb_at P t\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. etcb_at P t\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  done

lemma set_thread_state_runnable_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and (\<lambda>s. runnable ts)\<rbrace>
    set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_thread_state_runnable_valid_ready_qs set_thread_state_runnable_valid_release_q valid_idle_etcb_lift
                    set_thread_state_runnable_valid_sched_action simp: valid_sched_def)
  done

lemma set_thread_state_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. t \<in> S \<or> in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
                  \<or> scheduler_action s = switch_thread t
                  \<or> (runnable ts \<longrightarrow> \<not> active_sc_tcb_at t s)) \<rbrace>
      set_thread_state t ts
   \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: is_schedulable_wp set_object_wp get_object_wp
                    set_scheduler_action_valid_blocked_except_set_const)
  apply (rename_tac sched; case_tac sched; clarsimp)
  by (fastforce simp: is_schedulable_opt_def active_sc_tcb_at_defs st_tcb_at_kh_def in_queue_2_def
                       not_queued_def valid_blocked_except_set_def not_in_release_q_def
               split: option.splits if_splits dest!: get_tcb_SomeD)+ (* takes a while *)

lemma set_thread_state_not_runnable_valid_blocked_except_set_remove:
  "\<lbrace>valid_blocked_except_set (insert ref S) and K (\<not> runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. (valid_blocked_except_set S)::det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: set_scheduler_action_wp is_schedulable_wp set_object_wp)
  by (fastforce simp: is_schedulable_opt_def active_sc_tcb_at_defs st_tcb_at_kh_def in_queue_2_def
                       not_queued_def valid_blocked_except_set_def not_in_release_q_def
               split: option.splits if_splits dest!: get_tcb_SomeD)

lemmas set_thread_state_not_runnable_valid_blocked_strong =
       set_thread_state_valid_blocked_except_set_const

lemma set_thread_state_not_runnable_valid_blocked:
  "\<lbrace>valid_blocked and K (\<not> runnable ts)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> bool\<rbrace>"
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked_strong)

lemmas set_thread_state_not_runnable_valid_blocked_remove =
  set_thread_state_not_runnable_valid_blocked_except_set_remove

lemmas set_thread_state_valid_blocked_const =
  set_thread_state_valid_blocked_except_set_const

lemma set_thread_state_ready_queues[wp]:
  "\<lbrace>\<lambda>s :: det_state. P (ready_queues s)\<rbrace>
    set_thread_state thread ts
   \<lbrace>\<lambda>r s. P (ready_queues s)\<rbrace>"
  apply (simp add: set_thread_state_def )
  apply (simp add: set_thread_state_act_def[abs_def] reschedule_required_def
                   set_scheduler_action_def set_object_def)
  apply (wp | wpc | simp add: tcb_sched_action_def)+
  done

crunches set_thread_state
for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: set_object_wp ignore: set_object)

crunches set_thread_state_act
for is_refill_sufficient[wp]: "is_refill_sufficient scp u"
and is_refill_ready[wp]: "(\<lambda>s. Q (is_refill_ready p u s))::det_state \<Rightarrow> _"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and cur_time[wp]: "\<lambda>s. P (cur_time s) "
and kheap_cur_time[wp]: "\<lambda>s. P (kheap s) (cur_time s) "
  (wp: set_object_wp ignore: set_object)

lemma set_thread_state_is_refill_sufficient[wp]:
  "\<lbrace>is_refill_sufficient t u\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. is_refill_sufficient t u\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def is_refill_sufficient_def obj_at_def
                   get_tcb_def wp: hoare_vcg_ex_lift)


lemma set_thread_state_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s. P (budget_sufficient t s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def
                   get_tcb_def is_refill_sufficient_def wp: hoare_vcg_ex_lift
                split: option.splits)
  apply (intro conjI impI; clarsimp elim!: rsubst [where P=P]; intro conjI impI iffI; clarsimp)
  apply (rule_tac x=scp in exI; fastforce)
  apply (case_tac x2; clarsimp)
  by (rule_tac x=scp in exI; fastforce)


lemma set_thread_state_is_refill_ready[wp]:
  "\<lbrace>is_refill_ready t u\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. is_refill_ready t u\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def is_refill_ready_def obj_at_def
                   get_tcb_def wp: hoare_vcg_ex_lift)


lemma set_thread_state_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s. P (budget_ready t s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def
                   get_tcb_def is_refill_ready_def wp: hoare_vcg_ex_lift
                split: option.splits)
  apply (intro conjI impI; clarsimp elim!: rsubst [where P=P]; intro conjI impI iffI; clarsimp)
  apply (rule_tac x=scp in exI; fastforce)
  apply (case_tac x2; clarsimp)
  by (rule_tac x=scp in exI; fastforce)

lemma set_thread_state_active_valid_sched:
  "active st \<Longrightarrow>
   \<lbrace>valid_sched and ct_active and (\<lambda>s::det_state. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct st \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_ready_qs_def)
  apply (wp hoare_vcg_all_lift)
    apply (rule hoare_lift_Pf [where f="\<lambda>s. ready_queues s", OF _ set_thread_state_ready_queues])
    apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_cases simp: runnable_eq_active)
   apply (wp set_thread_state_runnable_valid_release_q
             set_thread_state_runnable_valid_sched_action set_thread_state_valid_blocked_const)
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def runnable_eq_active)
  done

lemma set_thread_state_Running_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s::det_state. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct Running \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule set_thread_state_active_valid_sched) simp

lemma set_thread_state_Restart_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s::det_state. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct Restart \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule set_thread_state_active_valid_sched) simp

lemma set_thread_state_act_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> set_thread_state_act tp  \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (clarsimp simp: set_thread_state_act_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_inv])
  apply (wpsimp simp: set_scheduler_action_def)
  done

crunch sched_act_not[wp]: set_thread_state "scheduler_act_not t"

lemma set_thread_state_not_runnable_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add:  set_object_def | wp)+
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split ct_not_in_q_def etcb_at_def
                        st_tcb_at_not active_sc_tcb_at_defs is_etcb_at'_def etcbs_of'_def
                        is_refill_sufficient_def is_refill_ready_def
                        refill_sufficient_kh_def refill_ready_kh_def
                  split: option.splits dest!: get_tcb_SomeD)

lemma set_thread_state_not_runnable_valid_release_q:
  "\<lbrace>valid_release_q and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add:  set_object_def | wp)+
  by (clarsimp simp: in_release_q_def get_tcb_rev
               dest!: get_tcb_SomeD cong: conj_cong) solve_valid_release_q

lemma set_thread_state_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: set_thread_state_act_not_valid_sched_action)

lemma set_thread_state_not_runnable_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not ref and K (\<not> runnable ts) and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_thread_state_not_runnable_valid_ready_qs
                   set_thread_state_act_not_valid_sched_action
                   set_thread_state_valid_blocked_const
                   set_thread_state_not_runnable_valid_release_q
               simp: valid_sched_def)

lemma set_thread_state_not_runnable_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and scheduler_act_not ref and K (\<not> runnable ts) and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_except_blocked :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_thread_state_not_runnable_valid_ready_qs
                   set_thread_state_act_not_valid_sched_action
                   set_thread_state_valid_blocked_const
                   set_thread_state_not_runnable_valid_release_q)

crunch simple_sched_action[wp]: set_thread_state_act,schedule_tcb simple_sched_action
  (wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma set_thread_state_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_thread_state param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: set_thread_state_def)

crunch not_cur_thread[wp]: schedule_tcb "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma set_thread_state_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread thread\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv. not_cur_thread thread\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_act_def  set_object_def
         wp: hoare_vcg_if_lift2 hoare_drop_imp gts_wp)+
  done

lemma set_thread_state_valid_release_q_except:
  "\<lbrace>valid_release_q\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_release_q_except thread\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp simp: set_scheduler_action_def wp: is_schedulable_wp set_object_wp)
  apply (subgoal_tac "valid_release_q_except_set_2
                      {thread}
                      (release_queue s)
                      (\<lambda>a. if a = thread then Some (TCB (y\<lparr>tcb_state := ts\<rparr>)) else kheap s a)")
   apply fastforce
  apply (clarsimp simp: sorted_release_q_def tcb_sched_dequeue_def valid_release_q_except_set_def valid_release_q_def)
  apply (rule conjI, clarsimp)
   apply (case_tac "t = thread"; clarsimp simp: Ball_def)
   apply (erule_tac x=t in allE; clarsimp)
   apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def active_sc_tcb_at_kh_def
                         bound_sc_tcb_at_kh_def test_sc_refill_max_kh_def st_tcb_at_def
                         obj_at_def active_sc_tcb_at_def pred_tcb_at_def test_sc_refill_max_def
                  split: option.splits
                  dest!: get_tcb_SomeD)
   apply (subgoal_tac "scp \<noteq> thread"; fastforce)
  by (fastforce elim!: sorted_wrt_mono_rel[rotated] simp: active_sc_tcb_at_defs
                dest!: get_tcb_SomeD)

lemma tcb_release_remove_valid_release_q_except:
  "\<lbrace>valid_release_q_except thread\<rbrace>
      tcb_release_remove thread
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding tcb_release_remove_def
  by (wpsimp;
      clarsimp simp: tcb_sched_dequeue_def valid_release_q_except_set_def
                     sorted_release_q_def valid_release_q_def)

lemma set_thread_state_sched_act_not_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and K (\<not>  runnable ts)
     and st_tcb_at (\<lambda>st. \<not> runnable st) thread\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: valid_sched_def |
      clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE |
      wp set_thread_state_not_runnable_valid_ready_qs
         set_thread_state_valid_blocked_const
         set_thread_state_not_runnable_valid_release_q
         set_thread_state_act_not_valid_sched_action)+

lemma set_thread_state_not_queued_valid_sched:
  "\<lbrace>valid_sched
    and \<comment> \<open>simple_sched_action and\<close> not_in_release_q thread
    and scheduler_act_not thread and not_queued thread
    and K (\<not>runnable ts)\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def |
      clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE |
      wp set_thread_state_not_queued_valid_ready_qs
         set_thread_state_valid_blocked_const
         set_thread_state_not_queued_valid_release_q
         set_thread_state_act_not_valid_sched_action)+

lemma set_thread_state_not_queued_valid_sched_strong:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except thread
    and \<comment> \<open>simple_sched_action and\<close> not_in_release_q thread
    and scheduler_act_not thread and not_queued thread
    and K (\<not>runnable ts)\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def |
      clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE |
      wp set_thread_state_not_queued_valid_ready_qs
         set_thread_state_not_runnable_valid_blocked_remove
         set_thread_state_not_queued_valid_release_q
         set_thread_state_act_not_valid_sched_action)+

crunches set_thread_state_act,schedule_tcb
for ct_active[wp]: ct_active
and obj_at[wp]: "obj_at P p"
and not_in_release_q[wp]: "\<lambda>s. P (not_in_release_q t s)"
and in_release_queue[wp]: "\<lambda>s. P (in_release_queue t s)"
and ct_not_in_release_q[wp]: "ct_not_in_release_q"
  (wp: crunch_wps ignore: set_object )

lemmas set_thread_state_active_valid_sched_except_blocked =
  set_thread_state_runnable_valid_sched_except_blocked[simplified runnable_eq_active]

lemma set_thread_state_runnable_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_thread_state_runnable_valid_ready_qs set_thread_state_valid_blocked_const
                    set_thread_state_runnable_valid_sched_action
                    set_thread_state_runnable_valid_release_q simp: valid_sched_def)
  (fastforce simp: valid_blocked_def runnable_eq_active pred_tcb_at_def obj_at_def)

lemma set_thread_state_break_valid_sched:  (* ref is previously blocked *)
  "\<lbrace>valid_sched and K (runnable ts)\<rbrace>
      set_thread_state ref ts\<lbrace>\<lambda>_. valid_sched_except_blocked and valid_blocked_except ref::det_state \<Rightarrow> bool\<rbrace>"
  apply (wpsimp wp: set_thread_state_runnable_valid_sched_except_blocked
                    set_thread_state_valid_blocked_except_set_const)
  apply (clarsimp simp: valid_sched_def)
  done

crunch ct_not_queued[wp]: set_thread_state "ct_not_queued::det_state \<Rightarrow> _" (wp: ct_not_queued_lift)
crunch ct_sched_act_not[wp]: set_thread_state "\<lambda>s. scheduler_act_not (cur_thread s) s"
  (wp: set_scheduler_action_wp gts_wp hoare_drop_imp
   simp: crunch_simps
   ignore: set_scheduler_action)

lemma set_thread_state_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. P (not_in_release_q t s)\<rbrace> set_thread_state tp ts \<lbrace>\<lambda>_ s. P (not_in_release_q t s)\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)

lemma set_thread_state_in_release_queue[wp]:
  "\<lbrace>\<lambda>s. P (in_release_queue t s)\<rbrace> set_thread_state tp ts \<lbrace>\<lambda>_ s. P (in_release_queue t s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  by (clarsimp simp: in_release_queue_def)

crunch ct_not_in_release_q[wp]: set_thread_state "ct_not_in_release_q"
  (wp: ct_not_in_release_q_lift)

crunches set_thread_state_act
  for valid_ep_q[wp]: valid_ep_q
  and valid_ntfn_q[wp]: valid_ntfn_q

lemma set_thread_state_ct_valid_ep_q:
  "\<lbrace> valid_ep_q and (\<lambda>s. thread = cur_thread s)\<rbrace> set_thread_state thread ts \<lbrace> \<lambda>_. valid_ep_q \<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ep_q_def dest!: get_tcb_SomeD split: option.splits)
  apply (drule_tac x=p in spec)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (drule_tac x=t in bspec, simp)
  apply (rule conjI, clarsimp simp: st_tcb_at_kh_if_split)
  apply (elim conjE disjE)
   apply (clarsimp simp: bound_sc_tcb_at_kh_if_split)
  apply (rule disjI2)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs option.splits)
  apply (rename_tac scp sc n)
  by (intro conjI; rule_tac x=scp in exI; fastforce)

lemma bound_sc_kh_budget_conditions_equiv:
  "active_sc_tcb_at_kh t kh = (\<exists>scp. bound_sc_tcb_at_kh (\<lambda>ko. ko = Some scp) t kh \<and> test_sc_refill_max_kh scp kh)"
  "budget_ready_kh curtime t kh = (\<exists>scp. bound_sc_tcb_at_kh (\<lambda>ko. ko = Some scp) t kh \<and> refill_ready_kh curtime scp 0 kh)"
  "budget_sufficient_kh t kh = (\<exists>scp. bound_sc_tcb_at_kh (\<lambda>ko. ko = Some scp) t kh \<and> refill_sufficient_kh scp kh)"
  unfolding bound_sc_tcb_at_kh_def obj_at_kh_def active_sc_tcb_at_kh_def
  by fastforce+

lemma bound_sc_budget_conditions_equiv:
  "active_sc_tcb_at t s = (\<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and> test_sc_refill_max scp s)"
  "budget_ready t s = (\<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and> is_refill_ready scp 0 s)"
  "budget_sufficient t s = (\<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and> is_refill_sufficient scp 0 s)"
  unfolding bound_sc_tcb_at_kh_def obj_at_kh_def active_sc_tcb_at_defs
  by fastforce+

lemma kh_budget_conditions_kheap_update_const:
  "t \<noteq> t' \<Longrightarrow>
   bound_sc_tcb_at_kh P t (\<lambda>a. if a = t' then X else kheap s a)
   = bound_sc_tcb_at_kh P t (kheap s)"
  "t \<noteq> t' \<Longrightarrow>
   test_sc_refill_max_kh t (\<lambda>a. if a = t' then X else kheap s a)
   = test_sc_refill_max_kh t (kheap s)"
  "t \<noteq> t' \<Longrightarrow>
   refill_sufficient_kh t (\<lambda>a. if a = t' then X else kheap s a)
   = refill_sufficient_kh t (kheap s)"
  "t \<noteq> t' \<Longrightarrow>
   refill_ready_kh ct t k (\<lambda>a. if a = t' then X else kheap s a)
   = refill_ready_kh ct t k (kheap s)"
  unfolding bound_sc_tcb_at_kh_def obj_at_kh_def test_sc_refill_max_kh_def refill_sufficient_kh_def
  by (fastforce simp: refill_ready_kh_def)+

lemma set_thread_state_ct_valid_ntfn_q:
  "\<lbrace> valid_ntfn_q and (\<lambda>s. thread = cur_thread s)\<rbrace> set_thread_state thread ts \<lbrace> \<lambda>_. valid_ntfn_q \<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ntfn_q_def dest!: get_tcb_SomeD split: option.splits)
  apply (drule_tac x=p in spec)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (drule_tac x=t in bspec, simp)
  apply (rule conjI)
   apply (elim conjE disjE)
    apply (clarsimp simp: bound_sc_tcb_at_kh_if_split)
   apply (intro disjI2; intro conjI)
     apply (clarsimp simp: bound_sc_kh_budget_conditions_equiv bound_sc_budget_conditions_equiv(1))
     apply (rule_tac x=scp in exI)
     apply (subst kh_budget_conditions_kheap_update_const, simp, subst kh_budget_conditions_kheap_update_const, clarsimp simp: test_sc_refill_max_def, clarsimp)
    apply (clarsimp simp: bound_sc_kh_budget_conditions_equiv bound_sc_budget_conditions_equiv(3))
    apply (rule_tac x=scp in exI)
    apply (subst kh_budget_conditions_kheap_update_const, simp, subst kh_budget_conditions_kheap_update_const, clarsimp simp: is_refill_sufficient_def obj_at_def, clarsimp)
   apply (clarsimp simp: bound_sc_kh_budget_conditions_equiv bound_sc_budget_conditions_equiv(2))
   apply (rule_tac x=scp in exI)
   apply (subst kh_budget_conditions_kheap_update_const, simp, subst kh_budget_conditions_kheap_update_const, clarsimp simp: is_refill_ready_def obj_at_def, clarsimp)
  apply (clarsimp simp: st_tcb_at_kh_if_split)
  done

lemma set_thread_state_ct_schedulability[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  "\<lbrace>\<lambda>s. budget_ready (cur_thread s) s\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s::det_state. budget_ready (cur_thread s) s\<rbrace>"
  "\<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_ s::det_state. budget_sufficient (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)+

(* set_tcb_obj_ref *)

lemma set_bound_notification_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                      etcb_defs refill_prop_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma set_bound_notification_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  by (clarsimp simp: get_tcb_rev dest!: get_tcb_SomeD) solve_valid_release_q

lemma set_tcb_sched_context_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and not_queued ref\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update ref sc \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma set_tcb_sched_context_valid_release_q_not_queued:
  "\<lbrace>valid_release_q and not_in_release_q ref\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update ref sc \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  by (clarsimp simp: not_in_release_q_def get_tcb_rev
               dest!: get_tcb_SomeD cong: conj_cong) solve_valid_release_q

lemma set_tcb_sched_context_valid_release_q_no_sc:
  "\<lbrace>valid_release_q and bound_sc_tcb_at ((=) None) ref\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update ref sc \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  by (clarsimp simp:  get_tcb_rev
               dest!: get_tcb_SomeD cong: conj_cong) solve_valid_release_q

lemma set_tcb_sched_context_valid_ready_qs_Some: (* when ref is in ready_queeus *)
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>d p. ref \<in> set (ready_queues s d p) \<longrightarrow>
              test_sc_refill_max sp s \<and> is_refill_sufficient sp 0 s \<and>  is_refill_ready sp 0 s)\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some sp) \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp dest!: get_tcb_SomeD split: option.splits
            simp: valid_ready_qs_def etcb_defs refill_prop_defs
                  st_tcb_at_kh_if_split active_sc_tcb_at_defs)
  by (intro impI conjI; fastforce dest!: get_tcb_SomeD simp: get_tcb_rev)+

lemma set_tcb_yield_to_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref ntfn \<lbrace>\<lambda>_. valid_ready_qs:: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma set_tcb_sched_context_valid_release_q_Some: (* when ref is in release_queue *)
  "\<lbrace>valid_release_q and
    (\<lambda>s. ref \<in> set (release_queue s)
         \<longrightarrow> test_sc_refill_max sp s
            \<and> tcb_ready_time ref s = scp_ready_time sp s) \<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some sp) \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  by (clarsimp simp: scp_ready_time_def dest!: get_tcb_SomeD) solve_valid_release_q

lemma set_tcb_yield_to_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref ntfn \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  by (clarsimp dest!: get_tcb_SomeD, solve_valid_release_q)

lemma set_bound_notification_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  done

lemma set_tcb_obj_ref_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> set_tcb_obj_ref f ref ntfn \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def)

lemma set_tcb_obj_ref_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. not_in_release_q t s\<rbrace> set_tcb_obj_ref f ref ntfn \<lbrace>\<lambda>_ s::det_state. not_in_release_q t s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def not_in_release_q_def)

lemma set_tcb_obj_ref_sc_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_release_q scp s \<and> (sc_opt = Some scp \<longrightarrow> not_in_release_q ref s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref sc_opt
   \<lbrace>\<lambda>_ s::det_state. sc_not_in_release_q scp s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def)
     (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD split: if_splits)

lemma set_bound_notification_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update ref ntfn
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_tcb_yield_to_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update ref ntfn
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_bound_notification_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp gbn_wp)+
  apply clarsimp
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done

lemma set_tcb_yield_to_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp gbn_wp)+
  apply clarsimp
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done

lemma set_bound_notification_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update ref ntfnptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  apply (rename_tac scp sc n)
  by (intro conjI impI; rule_tac x=scp in exI, fastforce)

lemma set_tcb_yield_to_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update ref tptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  apply (rename_tac scp sc n)
  by (intro conjI impI; rule_tac x=scp in exI, clarsimp)

lemma set_tcb_sched_context_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update ref ntfn
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_tcb_sched_context_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp gbn_wp)+
  apply clarsimp
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done

lemma set_tcb_sched_context_weak_valid_sched_action_weak:
  "\<lbrace>weak_valid_sched_action and (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0 ) scptr)
   and is_refill_ready scptr 0 and is_refill_sufficient scptr 0\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some scptr)
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_kh_if_split active_sc_tcb_at_defs refill_prop_defs
                        bound_sc_tcb_at_kh_if_split get_tcb_rev split: option.splits)
  by (intro conjI impI; (fastforce simp: active_sc_tcb_at_defs refill_prop_defs)?)+

lemma set_tcb_sched_context_simple_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and simple_sched_action\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def simple_sched_action_def dest!: get_tcb_SomeD)
  done

lemma set_tcb_obj_ref_ct_cur_domain[wp]:
  "set_tcb_obj_ref f ref ts \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  unfolding set_tcb_obj_ref_def set_object_def by wpsimp

lemma set_tcb_obj_ref_ct_in_cur_domain:
  "(\<And>tcb. etcb_of (f (K ts) tcb) = etcb_of tcb) \<Longrightarrow> set_tcb_obj_ref f ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding set_tcb_obj_ref_def set_object_def
  by wpsimp (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma set_bound_notification_cur_ct_in_cur_domain[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  by (simp add: set_tcb_obj_ref_ct_in_cur_domain)

lemma set_tcb_yield_to_cur_ct_in_cur_domain[wp]:
  "set_tcb_obj_ref tcb_yield_to_update ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  by (simp add: set_tcb_obj_ref_ct_in_cur_domain)

lemma set_tcb_sched_context_cur_ct_in_cur_domain[wp]:
  "set_tcb_obj_ref tcb_sched_context_update ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  by (simp add: set_tcb_obj_ref_ct_in_cur_domain)

lemma set_tcb_obj_ref_etcbs_all:
  "(\<And>tcb. tcb_priority tcb = tcb_priority (f (\<lambda>a. new) tcb) \<and> tcb_domain tcb = tcb_domain (f (\<lambda>a. new) tcb))
  \<Longrightarrow> set_tcb_obj_ref f ref new \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (auto dest!: get_tcb_SomeD simp: etcbs_of'_def elim!: rsubst[where P=P])
  done

lemmas set_tcb_bound_ntfn_etcbs[wp] =
  set_tcb_obj_ref_etcbs_all[where f=tcb_bound_notification_update, simplified]

lemmas set_tcb_sched_context_etcbs[wp] =
  set_tcb_obj_ref_etcbs_all[where f=tcb_sched_context_update, simplified]

lemmas set_tcb_tcb_yield_to_etcbs[wp] =
  set_tcb_obj_ref_etcbs_all[where f=tcb_yield_to_update, simplified]

lemma set_bound_notification_valid_sched_action:
  "\<lbrace>valid_sched_action\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_bound_notification_weak_valid_sched_action)+
  done

lemma set_tcb_yield_to_valid_sched_action:
  "set_tcb_obj_ref tcb_yield_to_update ref ntfn \<lbrace>valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_tcb_yield_to_weak_valid_sched_action)+
  done

lemma set_tcb_sched_context_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref scptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_tcb_sched_context_simple_weak_valid_sched_action)+
  done

lemma set_tcb_tcb_yield_to_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
    set_tcb_obj_ref tcb_yield_to_update ref scptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_tcb_yield_to_weak_valid_sched_action)+
  done

lemma set_tcb_sched_context_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not ref\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs
                        scheduler_act_not_def refill_prop_defs dest!: get_tcb_SomeD
                  split: option.splits)
 apply (rename_tac scp y)
   apply (intro conjI; rule_tac x= scp in exI; fastforce)
  done

lemma set_tcb_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action
    and (\<lambda>s. scheduler_action s = switch_thread ref
             \<longrightarrow> (\<exists>scp. scp_opt = Some scp \<and> test_sc_refill_max scp s
                      \<and> is_refill_sufficient scp 0 s \<and> is_refill_ready scp 0 s))\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp_opt
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  by (fastforce simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs get_tcb_rev
                        scheduler_act_not_def refill_prop_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma set_tcb_sched_context_valid_sched_action_Some:
  "\<lbrace>valid_sched_action and (\<lambda>s. scheduler_action s = switch_thread ref \<longrightarrow>
          test_sc_refill_max scp s \<and> is_refill_sufficient scp 0 s \<and> is_refill_ready scp 0 s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref (Some scp) \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_tcb_sched_context_weak_valid_sched_action)+
  done

lemma set_tcb_sched_context_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and scheduler_act_not ref\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def valid_sched_action_def st_tcb_at_kh_def
 in_cur_domain_def active_sc_tcb_at_defs scheduler_act_not_def is_activatable_2_def refill_prop_defs
 etcb_defs switch_in_cur_domain_def dest!: get_tcb_SomeD split: option.splits)
  by (intro conjI impI; fastforce dest!: get_tcb_SomeD simp: get_tcb_rev)

lemma set_bound_notification_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
    set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce simp: valid_blocked_except_set_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_def
           dest!: get_tcb_SomeD split: if_split_asm option.splits)

lemmas set_bound_notification_valid_blocked[wp] =
   set_bound_notification_valid_blocked_except_set[of "{}", simplified]

lemma set_tcb_sched_context_None_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update thread None
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce simp: not_in_release_q_def not_queued_def valid_blocked_except_def
                      st_tcb_at_kh_def active_sc_tcb_at_defs
               dest!: get_tcb_SomeD split: option.split_asm if_split_asm)

lemma set_tcb_sched_context_None_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update thread None
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce simp: not_in_release_q_def not_queued_def valid_blocked_except_def
                      st_tcb_at_kh_def active_sc_tcb_at_defs
               dest!: get_tcb_SomeD split: option.split_asm if_split_asm)

lemmas set_tcb_sched_context_None_valid_blocked_enqueue =
  set_tcb_sched_context_None_valid_blocked_except_set

lemmas set_tcb_sched_context_None_valid_blocked_const =
  set_tcb_sched_context_None_valid_blocked_except_set_const

lemma set_tcb_sched_context_valid_blocked_Some:
  "\<lbrace>valid_blocked and
    (\<lambda>s. not_queued t s \<and> not_in_release_q t s \<longrightarrow> st_tcb_at (\<lambda>ts. \<not>runnable ts) t s \<or> \<not> test_sc_refill_max sp s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t (Some sp) \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs runnable_eq_active
              dest!: get_tcb_SomeD
              split: if_split_asm option.splits)

lemma set_tcb_sched_context_valid_blocked:
  "\<lbrace>valid_blocked and
    (\<lambda>s. case sc_opt of Some sp \<Rightarrow>
            not_queued t s \<and> not_in_release_q t s \<longrightarrow> (\<not> st_tcb_at active t s) \<or> \<not> test_sc_refill_max sp s
          | _ \<Rightarrow> True)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc_opt \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_sched_context_valid_blocked_except_None_again:
  "\<lbrace>valid_blocked_except_set (insert t S)\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
  apply (drule_tac x=ta in spec, clarsimp)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_sched_context_Some_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some s)
   \<lbrace>\<lambda>_. valid_blocked_except t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
  apply (drule_tac x=ta in spec, clarsimp)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_sched_context_valid_blocked_except_None:
  "\<lbrace>valid_blocked_except t\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
  apply (drule_tac x=ta in spec, clarsimp)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_yield_to_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace> set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_except_set_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_pred_tcb_const:
  "\<forall>tcb. p (tcb_to_itcb (f (\<lambda>y. ntfn) tcb)) = p (tcb_to_itcb (tcb)) \<Longrightarrow>
  set_tcb_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (pred_tcb_at p P t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma set_tcb_obj_ref_obj_at_const:
  " \<forall>tcb. P (TCB (f (\<lambda>y. ntfn) tcb)) = P (TCB (tcb)) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q (obj_at P t s)\<rbrace> set_tcb_obj_ref f ref ntfn \<lbrace>\<lambda>_. (\<lambda>s. Q (obj_at P t s))::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp, clarsimp simp: obj_at_def)

lemma set_sc_obj_ref_obj_at_const:
  "\<forall>sc n. P (SchedContext (f (\<lambda>y. ntfn) sc) n) = P (SchedContext ( sc) n) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q (obj_at P t s)\<rbrace> set_sc_obj_ref f ref ntfn \<lbrace>\<lambda>_. (\<lambda>s. Q (obj_at P t s))::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_sc_obj_ref_wp, clarsimp simp: obj_at_def)

lemma set_tcb_active_sc_tcb_at_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>a. ntfn) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: active_sc_tcb_at_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_sc_active_sc_tcb_at_const:
  "\<forall>sc. sc_refill_max (f (\<lambda>y. ntfn) sc) = sc_refill_max (sc) \<Longrightarrow>
  set_sc_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_sc_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: active_sc_tcb_at_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_tcb_budget_sufficient_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>a. ntfn) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: budget_sufficient_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_sc_budget_sufficient_const:
  "\<forall>sc. sc_refills (f (\<lambda>y. ntfn) sc) = sc_refills (sc) \<Longrightarrow>
  set_sc_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_sc_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: budget_sufficient_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_tcb_obj_ref_budget_ready_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>a. ntfn) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: budget_ready_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_sc_obj_ref_budget_ready_const:
  "\<forall>sc. r_time (refill_hd (f (\<lambda>y. ntfn) sc)) = r_time (refill_hd (sc)) \<Longrightarrow>
  set_sc_obj_ref f ref ntfn \<lbrace>(\<lambda>s. Q (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_sc_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: budget_ready_defs cong: conj_cong)
  apply (fastforce)
  done

lemma set_tcb_obj_ref_valid_ntfn_q_const:
  "\<forall>tcb. tcb_state (f (\<lambda>y. ntfn) tcb) = tcb_state (tcb) \<and>
         tcb_sched_context (f (\<lambda>a. ntfn) tcb) = tcb_sched_context tcb \<Longrightarrow>
   set_tcb_obj_ref f ref ntfn \<lbrace>valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_ntfn_q_lift set_tcb_obj_ref_obj_at_const set_tcb_pred_tcb_const hoare_vcg_disj_lift set_tcb_active_sc_tcb_at_const set_tcb_budget_sufficient_const
                 set_tcb_obj_ref_budget_ready_const)

lemma set_sc_obj_ref_valid_ntfn_q_const:
  "\<forall>sc. sc_refills (f (\<lambda>a. ntfn) sc) = sc_refills sc
        \<and> sc_refill_max (f (\<lambda>y. ntfn) sc) = sc_refill_max (sc) \<Longrightarrow>
  set_sc_obj_ref f ref ntfn \<lbrace>valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_ntfn_q_lift set_sc_obj_ref_obj_at_const set_tcb_pred_tcb_const hoare_vcg_disj_lift set_sc_active_sc_tcb_at_const
                 set_sc_budget_sufficient_const set_sc_obj_ref_budget_ready_const)

lemma set_bound_notification_valid_ntfn_q:
  "set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_valid_ntfn_q_const)

lemma set_bound_notification_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def | wp set_bound_notification_valid_sched_action)+
  done

crunch ct_not_in_q[wp]: update_sched_context,set_sc_obj_ref,set_tcb_obj_ref ct_not_in_q

lemma set_tcb_yt_update_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update tptr scp \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  by (auto intro: budget_sufficient_set_object_no_change_tcb)

lemma set_tcb_yt_update_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update tptr scp \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  by (auto intro: budget_ready_set_object_no_change_tcb)

lemma set_tcb_yt_update_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update tptr scp \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  by (auto intro: active_sc_tcb_at_set_object_no_change_tcb)

crunch cur_time[wp]: set_tcb_obj_ref "\<lambda>s. P (cur_time s)"

lemma set_sc_test_sc_refill_max_indep:
  "\<forall>sc. (sc_refill_max ((f (\<lambda>_. tptr)) sc) > 0) \<longleftrightarrow> (sc_refill_max sc > 0)
   \<Longrightarrow> \<lbrace>\<lambda>s. P (test_sc_refill_max scp s)\<rbrace>
       set_sc_obj_ref f ref tptr
       \<lbrace>\<lambda>_ s. P (test_sc_refill_max scp s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: test_sc_refill_max_def obj_at_def)

lemma set_sc_tcb_test_sc_refill_max[wp]:
  "\<lbrace>\<lambda>s. P (test_sc_refill_max scp s)\<rbrace>
   set_sc_obj_ref sc_tcb_update ref tptr
   \<lbrace>\<lambda>_ s. P (test_sc_refill_max scp s)\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp set_sc_test_sc_refill_max_indep)

lemma set_sc_refills_is_refill_sufficient_indep:
  "\<forall>sc. sc_refills ((f (\<lambda>_. tptr)) sc) = sc_refills sc \<Longrightarrow>
       \<lbrace>is_refill_sufficient scp u\<rbrace>
     set_sc_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_sufficient scp u\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: is_refill_sufficient_def obj_at_def)

lemma set_sc_refills_is_refill_ready_indep:
  "\<forall>sc. sc_refills ((f (\<lambda>_. tptr)) sc) = sc_refills sc
   \<Longrightarrow> \<lbrace>is_refill_ready scp 0\<rbrace>
       set_sc_obj_ref f ref tptr
       \<lbrace>\<lambda>_. is_refill_ready scp 0\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: is_refill_ready_def obj_at_def)

lemma set_tcb_obj_ref_test_sc_refill_max[wp]:
  "\<lbrace>\<lambda>s. P (test_sc_refill_max scp s)\<rbrace>
     set_tcb_obj_ref f ref tptr \<lbrace>\<lambda>_ s. P (test_sc_refill_max scp s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: test_sc_refill_max_def dest!: get_tcb_SomeD)

lemma set_tcb_obj_ref_is_refill_ready[wp]:
  "\<lbrace>is_refill_ready scp 0\<rbrace>
     set_tcb_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_ready scp 0\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: is_refill_ready_def obj_at_def dest!: get_tcb_SomeD)

lemma set_tcb_obj_ref_is_refill_sufficient[wp]:
  "\<lbrace>is_refill_sufficient scp u\<rbrace>
     set_tcb_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_sufficient scp u\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: is_refill_sufficient_def obj_at_def dest!: get_tcb_SomeD)

lemma set_tcb_sc_update_active_sc_tcb_at_neq:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)
    \<and> (t\<noteq>tptr) \<rbrace>
      set_tcb_obj_ref tcb_sched_context_update tptr scopt \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def split: if_splits)
  by (intro conjI impI iffI; clarsimp simp: test_sc_refill_max_def split: if_splits option.splits, fastforce?)

lemma set_tcb_sc_update_active_sc_tcb_at_eq:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and>
   (active_sc_tcb_at t s \<longleftrightarrow> (\<exists>scp. scopt = Some scp \<and> test_sc_refill_max scp s)) \<rbrace>
      set_tcb_obj_ref tcb_sched_context_update t scopt \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def split: if_splits)
  by (intro conjI impI iffI; clarsimp simp: test_sc_refill_max_def split: if_splits option.splits, fastforce?)

lemma set_tcb_sched_context_valid_sched_not_queued_act_not:
  "\<lbrace>valid_sched and scheduler_act_not ref and not_queued ref and not_in_release_q ref
      and (\<lambda>s. case sc_opt of Some sp \<Rightarrow> \<not> test_sc_refill_max sp s | _ \<Rightarrow> True)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref sc_opt
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                  set_tcb_sched_context_valid_blocked
                    set_tcb_sched_context_valid_release_q_not_queued
                    set_tcb_sched_context_valid_sched_action_act_not
               simp : valid_sched_def split: option.splits)

lemma set_tcb_sched_context_valid_sched_not_in_release_q:
  "\<lbrace>valid_sched and tcb_at ref and not_in_release_q ref
    and (\<lambda>s. scheduler_action s = switch_thread ref
             \<longrightarrow> test_sc_refill_max scp s \<and> is_refill_sufficient scp 0 s \<and>  is_refill_ready scp 0 s)
    and (\<lambda>s. \<forall>d p. ref \<in> set (ready_queues s d p) \<longrightarrow>
              test_sc_refill_max scp s \<and> is_refill_sufficient scp 0 s \<and>  is_refill_ready scp 0 s)
    and (\<lambda>s. not_queued ref s \<and> not_in_release_q ref s \<longrightarrow>
                  st_tcb_at (\<lambda>ts. \<not>runnable ts) ref s \<or> \<not> test_sc_refill_max scp s)\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some scp)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_Some
                 set_tcb_sched_context_valid_blocked_Some
                 set_tcb_sched_context_valid_release_q_Some
                 set_tcb_sched_context_valid_sched_action_Some
               simp : valid_sched_def not_in_release_q_def)

lemma set_tcb_yield_to_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref scptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def
       | wp set_tcb_yield_to_valid_ready_qs
            set_tcb_yield_to_valid_sched_action)+
  done

crunches
  set_sc_obj_ref, tcb_sched_action, update_sched_context,
  set_tcb_obj_ref, tcb_release_remove, sched_context_donate
  for simple[wp]: simple_sched_action
  (simp: crunch_simps)

lemma set_tcb_sc_update_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t and (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0) scp) \<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr (Some scp) \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  by (rule_tac x=scpa in exI, clarsimp)

lemma ssc_sc_yf_update_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv  s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def wp: active_sc_tcb_at_update_sched_context_no_change)

lemma ssc_sc_yf_update_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def wp: budget_sufficient_update_sched_context_no_change)

lemma ssc_sc_yf_update_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def wp: budget_ready_update_sched_context_no_change)

lemma set_sc_tcb_update_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_sc_obj_ref sc_tcb_update scp tcb \<lbrace>\<lambda>rv  s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  by (rule_tac x=scpa in exI, clarsimp)

lemma set_sc_replies_update_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> set_sc_obj_ref sc_replies_update scp replies \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  by (rule_tac x=scpa in exI, clarsimp)

lemma set_sc_replies_update_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_sc_obj_ref sc_replies_update scp replies \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp elim!: rsubst[where P=P], rule iffI;
      fastforce simp: pred_tcb_at_def obj_at_def is_refill_ready_def split: if_splits)

lemma set_sc_replies_update_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> set_sc_obj_ref sc_replies_update scp replies \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp elim!: rsubst[where P=P], rule iffI;
      fastforce simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def split: if_splits)

lemma set_sc_replies_update_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P t\<rbrace> set_sc_obj_ref sc_replies_update scp replies \<lbrace>\<lambda>rv. sc_tcb_sc_at P t\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (auto simp: sc_tcb_sc_at_def pred_tcb_at_def obj_at_def)

(* as user schedule invariants *)

lemma as_user_valid_ready_qs[wp]: "\<lbrace>valid_ready_qs\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma as_user_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (wpsimp simp: as_user_def set_object_def)
  by (clarsimp dest!: get_tcb_SomeD) solve_valid_release_q

lemma as_user_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs bound_sc_tcb_at_kh_if_split get_tcb_rev
                 split: option.splits)
  apply (rename_tac scp sc n)
  by (intro conjI impI; rule_tac x=scp in exI; fastforce)

lemma as_user_is_activatable[wp]: "\<lbrace>is_activatable t\<rbrace> as_user ptr s \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (drule get_tcb_SomeD, auto)

lemma as_user_valid_sched_action[wp]: "\<lbrace>valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_sched_action_def st_tcb_at_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: is_activatable_def st_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
   apply (drule get_tcb_SomeD, clarsimp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  apply (rename_tac scp sc n)
  by (intro conjI impI; rule_tac x=scp in exI; fastforce)

lemma as_user_etcbs[wp]: "as_user ptr s \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  done

lemma as_user_ct_in_cur_domain[wp]: "\<lbrace>ct_in_cur_domain\<rbrace> as_user ptr s \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  done

lemma as_user_valid_blocked[wp]: "\<lbrace>valid_blocked\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
        split: option.splits dest!: get_tcb_SomeD)
  by (drule_tac x=t in spec, fastforce)

abbreviation
  cur_sc_in_release_q_imp_zero_consumed
where
  "cur_sc_in_release_q_imp_zero_consumed \<equiv>
    \<lambda>s. \<forall>t. bound_sc_tcb_at ((=) (Some (cur_sc s))) t s \<longrightarrow> in_release_q t s \<longrightarrow> consumed_time s = 0"

(* FIXME move to DetSchedInvs_AI *)
definition
  sc_is_round_robin :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_is_round_robin  = obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> (sc_period sc = sc_budget sc))"

locale DetSchedSchedule_AI =
  assumes arch_switch_to_idle_thread_valid_ready_qs'[wp]:
    "\<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  assumes arch_switch_to_thread_valid_ready_qs'[wp]:
    "\<And>t. \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_release_q'[wp]:
    "\<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  assumes arch_switch_to_thread_valid_release_q'[wp]:
    "\<And>t. \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  assumes arch_switch_to_thread_not_in_release_q[wp]:
    "\<And>t t'. \<lbrace>not_in_release_q t'::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. not_in_release_q t'\<rbrace>"
  assumes arch_switch_to_idle_thread_weak_valid_sched_action'[wp]:
    "\<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  assumes arch_switch_to_thread_weak_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  assumes switch_to_idle_thread_ct_not_in_q[wp]:
    "\<lbrace>valid_ready_qs and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_valid_sched_action[wp]:
    "\<lbrace>valid_sched_action and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_ct_in_cur_domain[wp]:
    "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_cur_sc_in_release_q_imp_zero_consumed[wp]:
    "\<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_sc_at_period[wp]:
    "\<And>p P. \<lbrace>sc_at_period P p\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. sc_at_period P p::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_t_thread_cur_sc_in_release_q_imp_zero_consumed[wp]:
    "\<And>t. \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_sc_at_period[wp]:
    "\<And>t p P. \<lbrace>sc_at_period P p\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. sc_at_period P p::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_is_activatable'[wp]:
    "\<And>t t'. \<lbrace>is_activatable t'\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. is_activatable t'::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>valid_sched_action\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_ct_in_cur_domain_2[wp]:
    "\<And>t' t.
      \<lbrace>\<lambda>s::det_state. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
        arch_switch_to_thread t
      \<lbrace>\<lambda>_ s. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>"
  assumes arch_switch_to_thread_valid_blocked[wp]:
    "\<And>t. \<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_blocked and ct_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_etcbs[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (etcbs_of s)\<rbrace>"
  assumes arch_switch_to_thread_cur_domain[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (cur_domain s)\<rbrace>"
  assumes arch_switch_to_thread_cur_sc[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (cur_sc s)\<rbrace>"
  assumes arch_switch_to_idle_thread_cur_sc[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. P (cur_sc s)\<rbrace>"
  assumes arch_switch_to_thread_cur_thread[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (cur_thread s)\<rbrace>"
  assumes arch_switch_to_idle_thread_cur_thread[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. P (cur_thread s)\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_idle[wp]:
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_idle::det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_ct_not_queued[wp]:
    "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  assumes switch_to_idle_thread_ct_not_in_release_q[wp]:
    "\<lbrace>valid_release_q and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s::det_state. ct_not_in_release_q s\<rbrace>"
  assumes make_arch_fault_msg_cur_thread[wp]:
    "\<And>P ft t. \<lbrace>\<lambda>s. P (cur_thread s) s\<rbrace>
      make_arch_fault_msg ft t
     \<lbrace>\<lambda>rv s::det_state. P (cur_thread s) s\<rbrace>"
  assumes switch_to_idle_thread_valid_blocked[wp]:
    "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_exst'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s. P (exst s :: det_ext)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>rv s. P (exst s)\<rbrace>"
  assumes arch_switch_to_thread_scheduler_action'[wp]:
    "\<And>P t.
      \<lbrace>\<lambda>s. P (scheduler_action (s :: det_ext state))\<rbrace>
        arch_switch_to_thread t
      \<lbrace>\<lambda>rv s. P (scheduler_action (s :: det_ext state))\<rbrace>"
  assumes stit_activatable':
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  assumes arch_switch_to_idle_thread_etcb_at'[wp]:
    "\<And>P t. \<lbrace>etcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. etcb_at P t::det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_cur_thread_idle_thread [wp]:
    "\<lbrace>\<top> :: det_ext state \<Rightarrow> bool\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  assumes arch_switch_to_idle_thread_scheduler_action'[wp]:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s::det_state. P (scheduler_action s)\<rbrace>"
  assumes arch_switch_to_idle_thread_release_queue[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. P (release_queue s)\<rbrace>"
  assumes arch_finalise_cap_ct_not_in_q'[wp]:
    "\<And>acap final. \<lbrace>ct_not_in_q\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_release_queue[wp]:
    "\<And>acap final P. arch_finalise_cap acap final \<lbrace>(\<lambda>s. P (release_queue s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_ready_queues[wp]:
    "\<And>acap final P. arch_finalise_cap acap final \<lbrace>(\<lambda>s. P (ready_queues s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_cur_thread[wp]:
    "\<And>acap final P. arch_finalise_cap acap final \<lbrace>(\<lambda>s. P (cur_thread s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_scheduler_action[wp]:
    "\<And>acap final P. arch_finalise_cap acap final \<lbrace>(\<lambda>s. P (scheduler_action s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_cur_sc_chargeable[wp]:
    "\<And>acap final. arch_finalise_cap acap final \<lbrace>cur_sc_chargeable ::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_simple_sched_action'[wp]:
    "\<And>acap final. \<lbrace>simple_sched_action\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_valid_sched'[wp]:
    "\<And>acap final. \<lbrace>valid_sched\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_valid_machine_time[wp]:
    "\<And>airq. arch_invoke_irq_control airq \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_valid_machine_time[wp]:
    "\<And>t p. arch_tcb_set_ipc_buffer t p \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_valid_machine_time[wp]:
    "\<And>c t. arch_post_modify_registers c t \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_valid_machine_time[wp]:
    "\<And>c x. arch_finalise_cap c x \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_ct_in_state[wp]:
    "\<And>c x P. arch_finalise_cap c x \<lbrace>ct_in_state P ::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_valid_sched'[wp]:
    "\<And>target ptr. \<lbrace>valid_sched\<rbrace> arch_tcb_set_ipc_buffer target ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_simple_sched_action'[wp]:
    "\<And>target ptr. \<lbrace>simple_sched_action\<rbrace> arch_tcb_set_ipc_buffer target ptr \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_valid_sched'[wp]:
    "\<And>f t x y. \<lbrace>valid_sched\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_active_sc_tcb_at[wp]:
    "\<And>f t x y a. handle_arch_fault_reply f t x y \<lbrace>(\<lambda>s. active_sc_tcb_at a s)::det_state \<Rightarrow> _\<rbrace>"
  assumes activate_thread_valid_sched:
    "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_valid_sched[wp]:
    "\<And>i.
      \<lbrace>invs and valid_sched and ct_active and valid_arch_inv i and
       (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
        arch_perform_invocation i
      \<lbrace>\<lambda>_.valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_cur_sc_chargeable[wp]:
    "\<And>i. arch_perform_invocation i \<lbrace>cur_sc_tcb_only_sym_bound::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_valid_machine_time[wp]:
    "\<And>i. arch_perform_invocation i \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_scheduler_action[wp]:
    "\<And>i P. arch_perform_invocation i \<lbrace>(\<lambda>s. P (scheduler_action s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_cur_thread[wp]:
    "\<And>i P. arch_perform_invocation i \<lbrace>(\<lambda>s. P (cur_thread s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_ready_queues[wp]:
    "\<And>i P. arch_perform_invocation i \<lbrace>(\<lambda>s. P (ready_queues s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_release_queue[wp]:
    "\<And>i P. arch_perform_invocation i \<lbrace>(\<lambda>s. P (release_queue s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_valid_sched'[wp]:
    "\<And>i. \<lbrace>valid_sched\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_cur_thread[wp]:
    "\<And>i P. arch_invoke_irq_control i \<lbrace>(\<lambda>s. P (cur_thread s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_scheduler_action[wp]:
    "\<And>i P. arch_invoke_irq_control i \<lbrace>(\<lambda>s. P (scheduler_action s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_release_queue[wp]:
    "\<And>i P. arch_invoke_irq_control i \<lbrace>(\<lambda>s. P (release_queue s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_ready_queues[wp]:
    "\<And>i P. arch_invoke_irq_control i \<lbrace>(\<lambda>s. P (ready_queues s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_cur_sc_chargeable[wp]:
    "\<And>i. arch_invoke_irq_control i \<lbrace>cur_sc_chargeable::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_valid_sched'[wp]:
    "\<And>t f. \<lbrace>valid_sched\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_not_queued'[wp]:
    "\<And>t' t f. \<lbrace>not_queued t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. not_queued t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_valid_machine_time[wp]:
    "\<And>t f. handle_vm_fault t f \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_cur_thread[wp]:
    "\<And>P t f. handle_vm_fault t f \<lbrace>\<lambda>s::det_state. P (cur_thread s)\<rbrace>"
  assumes handle_vm_fault_not_in_release_q'[wp]:
    "\<And>t' t f. \<lbrace>not_in_release_q t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. not_in_release_q t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_scheduler_act_not'[wp]:
    "\<And>t' t f. \<lbrace>scheduler_act_not t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. scheduler_act_not t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_not_queued'[wp]:
    "\<And>t' f t x y. \<lbrace>not_queued t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. not_queued t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_ct_not_queued'[wp]:
    "\<And>f t x y. \<lbrace>ct_not_queued\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_not_in_release_q'[wp]:
    "\<And>t' f t x y. \<lbrace>not_in_release_q t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. not_in_release_q t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_ct_not_in_release_q'[wp]:
    "\<And>f t x y. \<lbrace>\<lambda>s. not_in_release_q (cur_thread s) s\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_ s::det_state. not_in_release_q (cur_thread s) s\<rbrace>"
  assumes handle_arch_fault_reply_scheduler_act_not'[wp]:
    "\<And>t' f t x y. \<lbrace>scheduler_act_not t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. scheduler_act_not t'::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_simple_sched_action[wp]:
    "\<And>f t x y. \<lbrace>simple_sched_action\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_valid_ep_q[wp]:
    "\<And>f t x y. \<lbrace>valid_ep_q\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_cur'[wp]:
    "\<And>f t x y. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. cur_tcb::det_state \<Rightarrow> _\<rbrace>"
  assumes hvmf_st_tcb_at[wp]:
    "\<And>P t' t w.
      \<lbrace>st_tcb_at P t' :: det_ext state \<Rightarrow> bool \<rbrace>
        handle_vm_fault t w
      \<lbrace>\<lambda>rv. st_tcb_at P t' \<rbrace>"
  assumes arch_activate_idle_thread_valid_list'[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_list'[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_list'[wp]:
    "\<lbrace>valid_list\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_not_queued'[wp]:
    "\<And>t. \<lbrace>not_queued t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_not_in_release_q'[wp]:
    "\<And>t. \<lbrace>not_in_release_q t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_sc_not_in_ready_q'[wp]:
    "\<And>t. \<lbrace>sc_not_in_ready_q t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. sc_not_in_ready_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_sc_not_in_release_q'[wp]:
    "\<And>t. \<lbrace>sc_not_in_release_q t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. sc_not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_sc_is_round_robin[wp]:
    "\<And>P t. \<lbrace>\<lambda>s. P (sc_is_round_robin t s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s::det_state. P (sc_is_round_robin t s)\<rbrace>"
  assumes arch_switch_to_thread_sc_is_round_robin[wp]:
    "\<And>P t' t. \<lbrace>\<lambda>s. P (sc_is_round_robin t s)\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_ s::det_state. P (sc_is_round_robin t s)\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_machine_state[wp]:
    "\<lbrace>valid_machine_time\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_not_queued'[wp]:
    "\<And>t t'. \<lbrace>not_queued t\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_not_in_release_q'[wp]:
    "\<And>t t'. \<lbrace>not_in_release_q t\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_sc_not_in_ready_q'[wp]:
    "\<And>t t'. \<lbrace>sc_not_in_ready_q t\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. sc_not_in_ready_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_sc_not_in_release_q'[wp]:
    "\<And>t t'. \<lbrace>sc_not_in_release_q t\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. sc_not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_machine_state[wp]:
    "\<And>t. \<lbrace>valid_machine_time\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_release_queue[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>(\<lambda>s. P (release_queue s))::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_ready_queues[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>(\<lambda>s. P (ready_queues s))::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_cur_thread[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>(\<lambda>s. P (cur_thread s))::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_ct_in_state[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>ct_in_state P ::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_scheduler_action[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>(\<lambda>s. P (scheduler_action s))::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_cur_sc_chargeable[wp]:
    "\<And>t. prepare_thread_delete t \<lbrace>cur_sc_chargeable ::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_simple_sched_action'[wp]:
    "\<And>t. \<lbrace>simple_sched_action\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_valid_machine_time[wp]:
    "\<And>t. prepare_thread_delete t \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_not_cur_thread[wp] :
    "\<And>ft t t'. make_arch_fault_msg ft t \<lbrace>not_cur_thread t'::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_sched[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_ep_q[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_ready_qs[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_release_q[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_ct_not_in_q[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_ct_in_cur_domain[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_idle_etcb[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_idle_etcb::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_sched_action[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_weak_valid_sched_action[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_blocked_except_set[wp] :
    "\<And>ft t S. make_arch_fault_msg ft t \<lbrace>valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_scheduler_action[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes make_arch_fault_msg_valid_machine_time[wp] :
    "\<And>ft t. \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace> make_arch_fault_msg ft t \<lbrace>\<lambda>_. valid_machine_time\<rbrace>"
  assumes make_arch_fault_msg_ready_queues[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes make_arch_fault_msg_release_queue[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (release_queue s)\<rbrace>"
  assumes make_arch_fault_msg_active_sc_tcb_at[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_budget_ready[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_budget_sufficient[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_ct_active[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>ct_active::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_not_cur_thread[wp] :
    "\<And>ft t'. arch_get_sanitise_register_info ft \<lbrace>not_cur_thread t'::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_sched[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_ep_q[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_scheduler_action[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes arch_get_sanitise_register_info_ready_queues[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_get_sanitise_register_info_release_queue[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. P (release_queue s)\<rbrace>"
  assumes arch_get_sanitise_register_info_active_sc_tcb_at[wp] :
    "\<And>ft t. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. (active_sc_tcb_at t s)\<rbrace>"
  assumes arch_get_sanitise_register_info_budget_ready[wp] :
    "\<And>ft t. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. (budget_ready t s)\<rbrace>"
  assumes arch_get_sanitise_register_info_budget_sufficient[wp] :
    "\<And>ft t. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. (budget_sufficient t s)\<rbrace>"
  assumes arch_get_sanitise_register_info_cur'[wp]:
    "\<And>f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_get_sanitise_register_info f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_machine_time[wp]:
    "\<And>f. arch_get_sanitise_register_info f \<lbrace>\<lambda>s::det_state. valid_machine_time s\<rbrace>"
  assumes handle_arch_fault_reply_valid_machine_time[wp]:
    "\<And>a b c d. handle_arch_fault_reply a b c d \<lbrace>\<lambda>s::det_state. valid_machine_time s\<rbrace>"
  assumes arch_post_modify_registers_not_cur_thread[wp] :
    "\<And>c ft t'. arch_post_modify_registers c ft \<lbrace>not_cur_thread t'::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_valid_sched[wp] :
    "\<And>c ft. arch_post_modify_registers c ft \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_scheduler_action[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes arch_post_modify_registers_ready_queues[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_post_modify_registers_cur'[wp]:
    "\<And>c f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_post_modify_registers c f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_post_modify_registers_not_idle_thread[wp]:
    "\<And>c t. \<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  assumes arch_post_cap_deletion_valid_sched[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_machine_time[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_cur_sc_chargeable[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>cur_sc_chargeable ::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_ready_qs[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_release_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_ct_not_in_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_simple_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_active_sc_tcb_at[wp] :
    "\<And>c Q t. arch_post_cap_deletion c \<lbrace>(\<lambda>s. Q (active_sc_tcb_at t s)):: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_budget_ready[wp] :
    "\<And>c Q t. arch_post_cap_deletion c \<lbrace>(\<lambda>s. Q (budget_ready t s)):: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_budget_sufficient[wp] :
    "\<And>c Q t. arch_post_cap_deletion c \<lbrace>(\<lambda>s. Q (budget_sufficient t s)):: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_sched_act_not[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_queued[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_queued t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_release_queue[wp] :
    "\<And>P c. arch_post_cap_deletion c \<lbrace>(\<lambda>s. P (release_queue s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_ntfn_q[wp] :
    "\<And>P c. arch_post_cap_deletion c \<lbrace>valid_ntfn_q ::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_ep_q[wp] :
    "\<And>P c. arch_post_cap_deletion c \<lbrace>valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_cur_thread[wp] :
    "\<And>P c. arch_post_cap_deletion c \<lbrace>(\<lambda>s. P (cur_thread s))::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_weak_valid_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes  misc_dmo_valid_machine_time[wp]:
   "do_machine_op ackDeadlineIRQ \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a. do_machine_op (ackInterrupt a) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a. do_machine_op (maskInterrupt True a) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a b. do_machine_op (maskInterrupt a b) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a b. do_machine_op (clearMemory a b) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a b. do_machine_op (freeMemory a b) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
   "\<And>a b. do_machine_op (storeWord a b) \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  assumes update_time_stamp_valid_machine_time[wp]:
  "update_time_stamp \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  assumes dmo_getCurrentTime_vmt_sp[wp]:
  "\<lbrace>valid_machine_time :: det_state \<Rightarrow> _\<rbrace>
   do_machine_op getCurrentTime
   \<lbrace>\<lambda>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1)\<rbrace>"


context DetSchedSchedule_AI begin

lemma arch_switch_to_idle_thread_ct_in_release_q[wp]:
  "\<lbrace>\<lambda>s:: det_state. in_release_q (cur_thread s) s\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. \<lambda>s. in_release_q (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma make_arch_fault_msg_ct_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
   make_arch_fault_msg ft t
  \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma make_arch_fault_msg_ct_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. not_in_release_q (cur_thread s) s\<rbrace>
   make_arch_fault_msg ft t
   \<lbrace>\<lambda>rv s::det_state. not_in_release_q (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma handle_vm_fault_st_tcb_cur_thread[wp]:
  "\<lbrace> \<lambda>s :: det_ext state. st_tcb_at P (cur_thread s) s \<rbrace>
   handle_vm_fault t f
   \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_switch_to_idle_thread_ct_not_queued'[wp]:
  "\<lbrace>ct_not_queued\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_switch_to_idle_thread_ct_not_in_release_q'[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_release_q::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_switch_to_thread_ct_not_queued'[wp]:
  "\<lbrace>ct_not_queued\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_switch_to_thread_ct_not_in_release_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_release_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_release_q::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_get_sanitise_register_info_ct_not_queued[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_get_sanitise_register_info_ct_not_in_release_q[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. not_in_release_q (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma arch_switch_to_idle_thread_sc_not_in_ready_q_cur'[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_ready_q  (cur_sc s) s\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s::det_state. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma arch_switch_to_idle_thread_sc_not_in_release_q_cur'[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_release_q (cur_sc s) s\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s::det_state. sc_not_in_release_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma arch_switch_to_thread_sc_not_in_release_q_cur'[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_release_q (cur_sc s) s\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s::det_state. sc_not_in_release_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma arch_switch_to_thread_sc_sc_not_in_ready_q_cur'[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_ready_q (cur_sc s) s\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_ s::det_state. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)


crunches switch_to_idle_thread, switch_to_thread
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action wp: hoare_drop_imp tcb_sched_dequeue_valid_ready_qs)

crunch weak_valid_sched_action[wp]:
  switch_to_idle_thread, switch_to_thread "weak_valid_sched_action::det_state \<Rightarrow> _"
  (simp: whenE_def wp: hoare_drop_imp)

lemma arch_perform_invocation_scheduler_act_sane[wp]:
  "arch_perform_invocation iv \<lbrace>scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  by (wps, wpsimp)

end

lemma tcb_sched_dequeue_ct_not_in_q_2_ct_upd:
  "\<lbrace>valid_ready_qs\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s::det_state. ct_not_in_q_2 (ready_queues s) (scheduler_action s) thread\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: etcb_at_def ct_not_in_q_def valid_ready_qs_def tcb_sched_dequeue_def
                         not_queued_def
                   dest: ko_at_etcbD
                  split: option.split)
  done

lemma tcb_sched_dequeue_valid_sched_action_2_ct_upd:
  "\<lbrace>valid_sched_action and
       (\<lambda>s. is_activatable_2 thread (scheduler_action s) (kheap s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. valid_sched_action_2 (scheduler_action s) (kheap s) thread (cur_domain s) (cur_time s) (release_queue s)\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def valid_sched_action_def split: option.split)
  done

lemma tcb_dequeue_not_queued:
  "\<lbrace>valid_ready_qs\<rbrace> tcb_sched_action tcb_sched_dequeue tptr \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_dequeue_def)
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: hoare_drop_imp)
  by  (fastforce simp: etcb_defs tcb_sched_dequeue_def not_queued_def valid_ready_qs_def
               dest!: get_tcb_SomeD ko_at_etcbD
               split: option.splits cong: conj_cong imp_cong)

lemma tcb_release_remove_not_in_release_q[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_release_remove tptr \<lbrace>\<lambda>_. not_in_release_q tptr\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def not_in_release_q_def tcb_sched_dequeue_def)

lemma tcb_dequeue_not_queued_gen:
  "\<lbrace>not_queued tptr\<rbrace> tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)+
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_ready_qs_def
                  split: option.splits)
  done

context DetSchedSchedule_AI begin

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply wpsimp
  apply (clarsimp simp: valid_sched_def valid_ready_qs_def valid_sched_action_def
      st_tcb_at_kh_if_split st_tcb_def2 valid_blocked_def is_activatable_def
      split del: if_split cong: imp_cong conj_cong)
  apply (intro conjI impI allI)
      apply (drule_tac x=tptr in spec, clarsimp dest!: get_tcb_SomeD)
      apply (intro conjI impI allI; clarsimp simp: active_sc_tcb_at_defs split: option.splits)
             apply (drule_tac x=d and y=p in spec2, clarsimp)
             apply (drule_tac x=tptr in bspec)
              apply (clarsimp dest!: get_tcb_SomeD)
             apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
            apply (drule_tac x=d and y=p in spec2, clarsimp)
            apply (drule_tac x=tptr in bspec; clarsimp dest!: get_tcb_SomeD)
            apply (rule_tac x=scp in exI, fastforce)
           apply (drule_tac x=d and y=p in spec2, clarsimp)
           apply (fastforce simp: refill_sufficient_kh_def is_refill_sufficient_def obj_at_def
                                  etcb_defs dest!: get_tcb_SomeD split: option.splits)
          apply (drule_tac x=d and y=p in spec2, clarsimp)
          apply (fastforce simp: refill_ready_kh_def is_refill_ready_def etcb_defs obj_at_def
                           dest!: get_tcb_SomeD split: option.splits)
         apply (drule_tac x=d and y=p in spec2, clarsimp)
         apply (drule_tac x=t in bspec; clarsimp dest!: get_tcb_SomeD)
         apply (rename_tac scp ya)
         apply (rule_tac x=scp in exI, fastforce)
        apply (drule_tac x=d and y=p in spec2, clarsimp)
        apply (fastforce simp: refill_sufficient_kh_def is_refill_sufficient_def etcb_defs obj_at_def
                         dest!: get_tcb_SomeD split: option.splits)
       apply (drule_tac x=d and y=p in spec2, clarsimp)
       apply (fastforce simp: refill_ready_kh_def is_refill_ready_def etcb_defs obj_at_def
                        dest!: get_tcb_SomeD split: option.splits)
     apply solve_valid_release_q
     apply clarsimp
    apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split dest!: get_tcb_SomeD)
    apply (intro conjI impI allI;
           clarsimp simp: active_sc_tcb_at_defs refill_prop_defs
                   split: option.splits;
           rename_tac scp sc n; rule_tac x=scp in exI, clarsimp)
   apply (clarsimp simp: active_sc_tcb_at_defs dest!: get_tcb_SomeD split: option.splits if_split_asm)
   apply (drule_tac x=tptr in spec, clarsimp simp: get_tcb_rev)
  apply (drule_tac x=t in spec, clarsimp simp: get_tcb_rev)
  done

lemma switch_to_thread_ct_not_queued[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_thread_def)
  including no_pre
  apply wp
     prefer 12
     apply (rule get_wp)
    prefer 11
    apply (rule assert_inv)
   prefer 2
   apply (rule arch_switch_to_thread_valid_ready_qs')
  apply (wpsimp simp: tcb_sched_action_def thread_get_def
                   tcb_sched_dequeue_def)
defer
apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def)+
  by (fastforce simp: valid_ready_qs_def etcb_at_def not_queued_def
                      etcbs_of'_def is_etcb_at_def
               dest!: ko_at_etcbD get_tcb_SomeD
               split: option.splits)

lemma switch_to_thread_ct_not_in_release_q:
  "\<lbrace>\<top>\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::det_state. ct_not_in_release_q s\<rbrace>"
  by (wpsimp simp: switch_to_thread_def get_tcb_obj_ref_def thread_get_def)

end

context DetSchedSchedule_AI begin

lemma switch_to_thread_ct_not_in_q[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: ct_not_in_q_def2 not_queued_def[symmetric])
  apply (wp hoare_drop_imps | simp)+
  done

lemma switch_to_thread_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and is_activatable t\<rbrace>
     switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: tcb_sched_dequeue_valid_sched_action_2_ct_upd hoare_drop_imp
          simp: switch_to_thread_def)

end

lemma tcb_sched_dequeue_ct_in_cur_domain':
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_ s. ct_in_cur_domain (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  done

context DetSchedSchedule_AI begin

lemma as_user_ct_in_cur_domain_2[wp]:
  "as_user f t \<lbrace>\<lambda>s::det_state.
    ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>"
  unfolding as_user_def by (wpsimp wp: set_object_wp)

lemma switch_to_thread_ct_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
  switch_to_thread thread \<lbrace>\<lambda>_. ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wpsimp wp: tcb_sched_dequeue_ct_in_cur_domain' hoare_drop_imp)
  done

end

lemma tcb_sched_dequeue_valid_blocked_except_set':
  "\<lbrace>valid_blocked and ct_in_q\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_ s. valid_blocked (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_blocked_def not_in_release_q_def
                 dest!: ko_at_etcbD get_tcb_SomeD split: option.splits)
  apply (case_tac "t = cur_thread s")
   apply (simp add: ct_in_q_def)
   apply clarsimp
   apply (rule ccontr)
   apply clarsimp
   apply (erule impE)
    apply (case_tac st, (force simp: st_tcb_at_def obj_at_def not_in_release_q_def)+)[1]
   apply force
  apply (erule_tac x=t in allE)
  apply force
  done

context DetSchedSchedule_AI begin
lemma as_user_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> as_user tp S \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
      dest!: get_tcb_SomeD split: option.splits)
  apply (rule conjI, fastforce)
  apply (case_tac "tp = cur_thread s";
        clarsimp simp: not_in_release_q_def ct_in_q_def active_sc_tcb_at_defs)
  done
end

lemma do_machine_op_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_blocked and ct_in_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp | auto)+

context DetSchedSchedule_AI begin

lemma switch_to_thread_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp|wpc)+
     prefer 12
     apply (rule get_wp)
    prefer 11
    apply (rule assert_inv)
   prefer 2
   apply (rule arch_switch_to_thread_valid_blocked)
  by (wpsimp wp: tcb_sched_dequeue_ct_in_cur_domain'
      tcb_sched_dequeue_valid_blocked_except_set' hoare_drop_imp)+

crunch etcb_at[wp]: switch_to_thread "etcb_at P t::det_state \<Rightarrow> _"
  (wp: hoare_drop_imp)

lemma switch_to_thread_valid_sched:
  "\<lbrace>is_activatable t and in_cur_domain t and valid_sched_action and valid_ready_qs and valid_release_q and
    valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def | wp switch_to_thread_valid_blocked
       | simp add: ct_in_cur_domain_2_def)+
  done

crunch valid_idle[wp]: switch_to_idle_thread "valid_idle :: det_ext state \<Rightarrow> bool"

crunch scheduler_action[wp]: switch_to_thread "\<lambda>s. P (scheduler_action (s :: det_ext state))"
  (wp: hoare_drop_imp)

end

crunches update_cdt_list
  for valid_ready_qs[wp]: "valid_ready_qs"
  and ct_not_in_q[wp]: "ct_not_in_q"
  and weak_valid_sched_action[wp]: "weak_valid_sched_action"
  and valid_sched_action[wp]: "valid_sched_action"
  and valid_blocked[wp]: valid_blocked
  and valid_sched[wp]: "valid_sched"
  and valid_ep_q[wp]: "valid_ep_q"

crunches set_cdt, set_cap
  for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain::det_state \<Rightarrow> _"
  and ct_not_in_q[wp]: "ct_not_in_q::det_state \<Rightarrow> _"
  and weak_valid_sched_action[wp]: "weak_valid_sched_action::det_state \<Rightarrow> _"
  and valid_sched_action[wp]: "valid_sched_action::det_state \<Rightarrow> _"
  and valid_blocked[wp]: "valid_blocked::det_state \<Rightarrow> _"
    (wp: valid_ready_qs_lift valid_release_q_lift ct_not_in_q_lift weak_valid_sched_action_lift
         valid_sched_action_lift valid_blocked_lift valid_sched_lift set_cap_typ_at
         ct_in_cur_domain_lift valid_ep_q_lift)

crunches set_cdt, set_cap
  for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
    (wp: valid_ready_qs_lift ct_not_in_q_lift weak_valid_sched_action_lift
         valid_sched_action_lift valid_blocked_lift valid_sched_lift set_cap_typ_at
         ct_in_cur_domain_lift valid_ep_q_lift)


crunch ct_not_in_q[wp]: cap_insert "ct_not_in_q :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps)

crunch weak_valid_sched_action[wp]: cap_insert "weak_valid_sched_action :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps)

lemma guarded_switch_to_lift:
  "\<lbrace>P\<rbrace> switch_to_thread thread \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> guarded_switch_to thread \<lbrace>Q\<rbrace>"
  by (wpsimp wp: get_sched_context_wp
           simp: guarded_switch_to_def is_schedulable_def get_thread_state_def thread_get_def)

lemma next_domain_valid_idle[wp]:
  "\<lbrace> valid_idle \<rbrace> next_domain \<lbrace> \<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: next_domain_def wp: dxo_wp_weak)
  by (clarsimp simp: valid_idle_def Let_def)

lemma enqueue_thread_queued:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp 0 s \<and> is_refill_sufficient scp 0 s)) thread s\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. thread \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def obj_at_def pred_tcb_at_def
                        is_refill_ready_def is_refill_sufficient_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

lemma enqueue_nonempty:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp 0 s \<and> is_refill_sufficient scp 0 s)) thread s\<rbrace>
   tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. ready_queues s d prio \<noteq> [])\<rbrace>"
  by (rule hoare_post_imp[OF _ enqueue_thread_queued], metis empty_iff empty_set)

context DetSchedSchedule_AI begin

crunches switch_to_idle_thread
  for etcb_at[wp]: "etcb_at P t :: det_state \<Rightarrow> _"

(* FIXME move *)
lemma in_release_q_valid_blocked_ct_upd:
  "\<lbrakk>in_release_q (cur_thread s) s; valid_blocked s\<rbrakk> \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  apply (clarsimp simp: valid_blocked_def ct_in_state_def)
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply (case_tac "t=cur_thread s")
   apply (simp add: not_queued_def not_in_release_q_def in_release_q_def)
   apply (case_tac st, (force simp: st_tcb_at_def obj_at_def)+)
   done

(* there is no thread in the scheduler queue that can be switched to
    \<longleftrightarrow> ct is not schedulable
lemma switch_to_idle_thread_valid_blocked:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace>
    switch_to_idle_thread
   \<lbrace>\<lambda>rv s::det_state. valid_blocked s\<rbrace>"
  unfolding switch_to_idle_thread_def
  apply (wp| strengthen ct_in_q_valid_blocked_ct_upd)+
  apply (wpsimp wp: hoare_vcg_conj_lift)+
  done*)

lemma switch_to_idle_thread_valid_sched: (* ct is not schedulable *)
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q
    and valid_blocked and valid_idle_etcb and ct_in_q\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp valid_idle_etcb_lift switch_to_idle_thread_valid_blocked)+

crunch etcb_at[wp]: choose_thread "etcb_at P t :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma choose_thread_valid_sched[wp]:
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q
     and valid_blocked and ct_in_q
     and valid_idle_etcb\<rbrace>
     choose_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: choose_thread_def)
  apply (wp guarded_switch_to_lift switch_to_idle_thread_valid_sched switch_to_thread_valid_sched)
  apply (clarsimp simp: valid_ready_qs_def next_thread_def is_activatable_2_def
                 dest!: next_thread_queued)
  apply (fastforce simp: st_tcb_def2 in_cur_domain_def etcb_at_def split: option.splits)
  done

end

lemma tcb_sched_enqueue_in_cur_domain:
  "\<lbrace>in_cur_domain w\<rbrace> tcb_sched_action tcb_sched_enqueue t \<lbrace>\<lambda>_. in_cur_domain w\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def in_cur_domain_def thread_get_def)+
  done

crunches next_domain
for valid_ready_qs: "valid_ready_qs"
and valid_release_q: "valid_release_q"
and valid_blocked: "valid_blocked"
 (simp: Let_def wp: dxo_wp_weak)

lemma next_domain_ct_in_q: "\<lbrace>ct_in_q\<rbrace> next_domain \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (clarsimp simp: next_domain_def)
  apply (wpsimp wp: dxo_wp_weak simp: ct_in_q_def)
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def etcb_at_def active_sc_tcb_at_defs)
  done

crunch ct_not_in_q: next_domain "ct_not_in_q" (simp: Let_def wp: dxo_wp_weak)

lemma next_domain_valid_sched_action:
  "\<lbrace>\<lambda>s. scheduler_action s = choose_new_thread\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: next_domain_def thread_set_domain_def)
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: Let_def valid_sched_action_def weak_valid_sched_action_def etcb_at_def)
  done

lemma tcb_sched_dequeue_in_cur_domain:
  "\<lbrace>in_cur_domain thread\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_. in_cur_domain thread\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  done

context DetSchedSchedule_AI begin

lemma arch_switch_to_thread_cur_domain_etcbs[wp]:
  "arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (cur_domain s) (etcbs_of s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_domain], rule hoare_lift_Pf[where f=etcbs_of]; wp)

lemma switch_to_thread_cur_in_cur_domain[wp]:
  "\<lbrace>in_cur_domain t\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_ s::det_state. in_cur_domain (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_thread_def | wp hoare_drop_imp tcb_sched_dequeue_in_cur_domain)+
  done
end

lemma tcb_sched_enqueue_cur_ct_in_q:
  "\<lbrace>\<lambda>s. cur = cur_thread s\<rbrace>
       tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)+
  apply (fastforce simp: etcb_at_def ct_in_q_def tcb_sched_enqueue_def active_sc_tcb_at_def
                        obj_at_def pred_tcb_at_def is_refill_ready_def is_refill_sufficient_def
                 dest!: get_tcb_SomeD split: option.splits)
  done

lemma tcb_sched_enqueue_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_enqueue_def split: option.splits)
  done

lemma tcb_sched_append_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_append cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)+
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_append_def split: option.splits)
  done

context DetSchedSchedule_AI begin
crunches switch_to_idle_thread, next_domain
  for scheduler_action[wp]: "\<lambda>s::det_state. P (scheduler_action s)"
  and not_queued[wp]: "not_queued t::det_state \<Rightarrow> _"
  and not_in_release_q[wp]: "not_in_release_q t::det_state \<Rightarrow> _"
  and sc_not_in_ready_q[wp]: "sc_not_in_ready_q t::det_state \<Rightarrow> _"
  and sc_not_in_release_q[wp]: "sc_not_in_release_q t::det_state \<Rightarrow> _"
  and ct_not_queued[wp]: "ct_not_queued::det_state \<Rightarrow> _"
  and ct_not_in_release_q[wp]: "ct_not_in_release_q::det_state \<Rightarrow> _"
  and sc_not_in_ready_q_cur[wp]: "\<lambda>s::det_state. sc_not_in_ready_q (cur_sc s) s"
  and sc_not_in_release_q_cur[wp]: "\<lambda>s::det_state. sc_not_in_release_q (cur_sc s) s"
    (simp: Let_def wp: dxo_wp_weak)
end

context DetSchedSchedule_AI begin
lemma switch_to_thread_sched_act_is_cur:
  "\<lbrace>\<lambda>s::det_state. scheduler_action s = switch_thread word\<rbrace> switch_to_thread word
       \<lbrace>\<lambda>rv s. scheduler_action s = switch_thread (cur_thread s)\<rbrace>"
  by (wpsimp simp: switch_to_thread_def wp: hoare_drop_imp)
end

crunch valid_idle_etcb[wp]: next_domain "valid_idle_etcb"
  (simp: Let_def wp: dxo_wp_weak)

lemma set_scheduler_action_switch_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action (switch_thread t) \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: ct_not_in_q_def)
  done

lemma possible_switch_to_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace> possible_switch_to t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp simp: not_cur_thread_def)
  done

crunch ct_not_in_q[wp]: tcb_release_remove ct_not_in_q
crunch ct_not_in_q[wp]: test_reschedule ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_vcg_if_lift2)

lemma sched_context_donate_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def)

lemma sched_context_unbind_tcb_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> sched_context_unbind_tcb scp \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: sched_context_unbind_tcb_def)
  apply (wpsimp wp: get_sched_context_wp)
  done

crunch ct_not_in_q[wp]: reply_unlink_sc ct_not_in_q
  (wp: crunch_wps hoare_drop_imps)

crunch ct_not_in_q[wp]: reply_unlink_tcb ct_not_in_q
  (wp: crunch_wps hoare_drop_imps)

lemma reply_remove_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> reply_remove t r \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)
  done

lemma update_sched_context_valid_ready_qs:
  "\<lbrace>valid_ready_qs and
        (\<lambda>s. \<forall>t. bound_sc_tcb_at ((=) (Some ref)) t s
           \<longrightarrow> in_ready_q t s
           \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs sufficient_refills_def
                      active_sc_tcb_at_defs st_tcb_at_kh_if_split in_ready_q_def refills_capacity_def
               split: option.splits)

lemma update_sched_context_valid_release_q:
  "\<lbrace>valid_release_q
     and (\<lambda>s.  \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
         \<longrightarrow> in_release_q t s
         \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                     \<longrightarrow> ((0 < sc_refill_max sc) = (0 < sc_refill_max (f sc))
                          \<and> r_time (refill_hd sc) = r_time (refill_hd (f sc)))))\<rbrace>
   update_sched_context sc_ptr f \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp simp: active_sc_tcb_at_defs get_tcb_rev in_release_q_def
               dest!: get_tcb_SomeD) solve_valid_release_q

lemma update_sched_context_valid_release_q_not_in_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q ref\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp wp: update_sched_context_valid_release_q
           simp: not_in_release_q_def in_release_q_def)

(* FIXME: The proof of this lemma should be scrapped or improved when valid_ipc_q invariants
          are updated *)
lemma update_sched_context_valid_ep_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
                    \<longrightarrow> in_ep_q t s
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: valid_ep_q_def obj_at_def in_ep_q_def split: option.splits if_splits)
  apply (drule_tac x=p in spec, clarsimp)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split, clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (erule disjE)
   apply (intro disjI1)
   apply (clarsimp simp: bound_sc_tcb_at_kh_if_split, clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (intro disjI2)
  apply (subgoal_tac "(\<exists>ptr. ep_at_pred (\<lambda>ep. t \<in> set (ep_queue ep)) ptr s) \<and> t \<noteq> sc_ptr")
   apply (intro conjI)
     apply (clarsimp simp: active_sc_tcb_at_kh_if_split test_sc_refill_max_kh_if_split)
     apply (clarsimp simp: active_sc_tcb_at_defs)
     apply (rule_tac x=scpb in exI, clarsimp)
    apply (clarsimp simp: budget_sufficient_kh_if_split refill_sufficient_kh_if_split)
    apply (clarsimp simp: active_sc_tcb_at_defs sufficient_refills_def is_refill_sufficient_def refills_capacity_def)
    apply (rule_tac x=scpb in exI, clarsimp)
   apply (clarsimp simp: budget_ready_kh_if_split refill_ready_kh_if_split)
   apply (clarsimp simp: active_sc_tcb_at_defs is_refill_ready_def)
   apply (rule_tac x=scpb in exI, clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: simple_obj_at_def, fastforce)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def)
  done

lemma update_sched_context_valid_ep_q_not_in_ep_q:
  "\<lbrace>valid_ep_q and sc_not_in_ep_q sc_ptr\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  by (wpsimp wp: update_sched_context_valid_ep_q)

lemma update_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action
    and (\<lambda>s.  \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s
            \<longrightarrow> scheduler_action s = switch_thread tcb_ptr
            \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
      update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (fastforce simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs
                      sufficient_refills_def refills_capacity_def refill_prop_defs
                split: option.splits  dest!: get_tcb_SomeD)

lemma update_sched_context_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: update_sched_context_weak_valid_sched_action
           simp: scheduler_act_not_def) fastforce

lemma update_sched_context_weak_valid_sched_action_simple_sched_action:
  "\<lbrace>weak_valid_sched_action and simple_sched_action\<rbrace>
   update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: update_sched_context_weak_valid_sched_action_act_not)

lemma update_sched_context_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      update_sched_context ref f \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def etcbs_of'_non_tcb_update a_type_def obj_at_def wp: get_object_wp)
  done

lemma update_sched_context_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     update_sched_context ref f
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp set_scheduler_action_wp)
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma update_sched_context_valid_sched_action:
  "\<lbrace>valid_sched_action
   and (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s
            \<longrightarrow> scheduler_action s = switch_thread tcb_ptr
            \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                       \<longrightarrow> 0 < sc_refill_max (f sc)
                         \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
                         \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
      update_sched_context sc_ptr f \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_action_def obj_at_def
               wp: update_sched_context_weak_valid_sched_action)

lemma update_sched_context_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: update_sched_context_valid_sched_action
           simp: scheduler_act_not_def) fastforce

lemma update_sched_context_valid_sched_action_simple_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   update_sched_context ref f
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: update_sched_context_valid_sched_action_act_not)
  done

lemma update_sched_context_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     update_sched_context ptr f
   \<lbrace>\<lambda>_ . ct_in_cur_domain\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp set_scheduler_action_wp)
  apply (clarsimp simp: etcbs_of'_non_tcb_update a_type_def obj_at_def)
  done

lemma update_sched_context_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and
   (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = Some sc_ptr) tcb_ptr s
    \<longrightarrow> (not_queued tcb_ptr s \<and> not_in_release_q tcb_ptr s \<and> scheduler_act_not tcb_ptr s)
    \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
         \<longrightarrow> (sc_refill_max sc > 0 \<longleftrightarrow> sc_refill_max (f sc) > 0)))\<rbrace>
     update_sched_context sc_ptr f \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (fastforce simp: valid_blocked_except_set_def scheduler_act_not_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
    dest!: get_tcb_SomeD split: if_split_asm option.splits)

lemma update_sched_context_valid_blocked:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow> sc_refill_max (f sc) > 0 \<longrightarrow> sc_refill_max sc > 0)\<rbrace>
   update_sched_context ptr f
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_blocked_def)
  apply (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)
  done

lemma update_sched_context_etcb_at[wp]:
  "update_sched_context p f \<lbrace>etcb_at P t\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: etcbs_of'_non_tcb_update a_type_def obj_at_def)
  done

lemma update_sched_context_valid_blocked_except_set_except:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>tcb_ptr.  bound_sc_tcb_at (\<lambda>t. t = (Some sc_ptr)) tcb_ptr s \<longrightarrow> tcb_ptr \<in> S)\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_blocked_except_set_def)
  apply (drule_tac x=t in spec, clarsimp)
  apply (drule_tac x=t in spec, clarsimp)
  apply (clarsimp simp: active_sc_tcb_at_defs st_tcb_at_kh_def split: option.splits if_splits)
  done

lemma set_sc_ntfn_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_sc_obj_ref sc_ntfn_update p new \<lbrace>\<lambda>_. valid_ntfn_q :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_sc_obj_ref_valid_ntfn_q_const)

lemma update_sched_context_valid_sched:
  "\<lbrace>valid_sched and K (\<forall>sc. (0 < sc_refill_max sc) = (0 < sc_refill_max (f sc)))
   and (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s
            \<longrightarrow> scheduler_action s = switch_thread tcb_ptr
            \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                       \<longrightarrow> 0 < sc_refill_max (f sc)
                         \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
                         \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))
    and (\<lambda>s. \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
           \<longrightarrow> in_ready_q t s
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> MIN_BUDGET \<le> r_amount (hd (sc_refills (f sc)))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))
     and (\<lambda>s.  \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
         \<longrightarrow> in_release_q t s
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow> ((0 < sc_refill_max sc) = (0 < sc_refill_max (f sc))
                                 \<and> r_time (refill_hd sc) = r_time (refill_hd (f sc)))))
    and (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s
    \<longrightarrow> (not_queued tcb_ptr s \<and> not_in_release_q tcb_ptr s \<and> scheduler_act_not tcb_ptr s)
    \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
         \<longrightarrow> (sc_refill_max sc > 0 \<longleftrightarrow> sc_refill_max (f sc) > 0)))\<rbrace>
    update_sched_context sc_ptr f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def
             wp: update_sched_context_valid_ready_qs update_sched_context_valid_release_q valid_idle_etcb_lift
                 update_sched_context_valid_sched_action update_sched_context_valid_blocked)

(* set_refills lemmas *)

lemma set_refills_valid_ready_qs:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ready_q tcb_ptr s \<longrightarrow> (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_valid_ready_qs)
  by (fastforce simp: valid_ready_qs_def refill_prop_defs
                      active_sc_tcb_at_defs in_ready_q_def
                      sufficient_refills_def refills_capacity_def
               split: option.splits)

lemma set_refills_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and sc_not_in_ready_q sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: set_refills_valid_ready_qs simp: in_queue_2_def not_queued_def)

lemma set_refills_valid_release_q:
  "\<lbrace>valid_release_q
     and (\<lambda>s.  \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
         \<longrightarrow> in_release_q t s
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s
                              \<longrightarrow> r_time (refill_hd sc) = r_time (hd refills)))\<rbrace>
   set_refills sc_ptr refills \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_refills_def)
  apply (wpsimp wp: update_sched_context_valid_release_q)
  by (fastforce simp: active_sc_tcb_at_defs get_tcb_rev in_release_q_def valid_release_q_def
               dest!: get_tcb_SomeD split: option.splits)


lemma set_refills_valid_release_q_not_in_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wpsimp wp: set_refills_valid_release_q simp: not_in_release_q_def in_release_q_def)

lemma set_refills_sc_tcb_sc_at[wp]:
  "set_refills sc_ptr' refills \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp )
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma set_refills_budget_ready:
  "\<lbrace>budget_ready t and
    (\<lambda>s. bound_sc_tcb_at ((=) (Some sc_ptr)) t s \<longrightarrow>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs is_refill_ready_def split: option.splits
                  cong: conj_cong |safe)+
  apply (rule_tac x=scp in exI, clarsimp)
  done

lemma set_refills_budget_sufficient:
  "\<lbrace>budget_sufficient t and
    (\<lambda>s. bound_sc_tcb_at ((=) (Some sc_ptr)) t s \<longrightarrow>
                   MIN_BUDGET \<le> r_amount (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs is_refill_sufficient_def
                        sufficient_refills_def refills_capacity_def
                 split: option.splits
                  cong: conj_cong |safe)+
  apply fastforce
  done

lemma set_refills_budget_ready_other:
  "\<lbrace>budget_ready t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x \<noteq> (Some sc_ptr)) t s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_ready_def)

lemma set_refills_budget_sufficient_other:
  "\<lbrace>budget_sufficient t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x \<noteq> (Some sc_ptr)) t s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)

(* FIXME: improve abstraction (ko_at_Endpoint could be simple_ko_at) *)
lemma set_refills_ko_at_Endpoint[wp]:
  "set_refills sc_ptr refills \<lbrace>\<lambda>s. \<not> ko_at (Endpoint ep) p s\<rbrace>"
  unfolding set_refills_def
  by (wpsimp wp: update_sched_context_wp simp: obj_at_def)

(* FIXME maybe move? *)
lemma valid_ep_q_def2:
  "(valid_ep_q s) = (\<forall>p t. ep_at_pred (\<lambda>ep. t \<in> set (ep_queue ep)) p s \<longrightarrow> (st_tcb_at_kh
                       (\<lambda>ts. (\<exists>eptr r_opt. ts = BlockedOnReceive eptr r_opt) \<or> (
                              \<exists>eptr pl. ts = BlockedOnSend eptr pl))
                       t (kheap s) \<and>
                      t \<noteq> cur_thread s \<and>
                      t \<noteq> idle_thread s \<and>
                      has_budget_kh t (cur_time s) (kheap s)))"
  apply (clarsimp simp: valid_ep_q_def obj_at_def simple_obj_at_def split: option.splits)
  apply (intro iffI; clarsimp)
  apply (drule_tac x=p and y="Endpoint obj" in spec2, simp)
  apply (case_tac x2; fastforce)
  done

(* FIXME move *)

definition has_budget where
  "has_budget t \<equiv> \<lambda>s. has_budget_kh t (cur_time s) (kheap s)"

lemma has_budget_equiv:
  "has_budget t = (tcb_at t and
                  (\<lambda>s. bound_sc_tcb_at bound t s  \<longrightarrow>
                       active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s))"
  apply (clarsimp simp: has_budget_def pred_tcb_at_eq_commute fun_eq_iff
                        iff_conv_conj_imp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb)
  done

lemma has_budget_equiv2: (* to make the current has_budget/has_budget_kh definition more usable *)
  "has_budget t = (\<lambda>s. bound_sc_tcb_at ((=) None) t s \<or>
                       active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)"
  apply (clarsimp simp: has_budget_def pred_tcb_at_eq_commute fun_eq_iff
                        iff_conv_conj_imp)
  done

crunches set_refills
for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
and ct_not_in_q[wp]: "ct_not_in_q"
and ct_in_cur_domain[wp]: "ct_in_cur_domain"

lemma set_refills_etcb_at[wp]:
  "set_refills scp rf \<lbrace>etcb_at P t\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma update_sc_refills_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
     update_sched_context scptr (\<lambda>sc. sc\<lparr>sc_refills := (f sc)\<rparr>) \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  by (intro conjI impI, clarsimp, rule_tac x=scp in exI, fastforce)

lemma set_refills_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     set_refills scptr new \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_valid_ep_q:
  "\<lbrace>valid_ep_q and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ep_q tcb_ptr s \<longrightarrow>
                   (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                    r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ep_q\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_valid_ep_q)
  apply (drule_tac x=t in spec, clarsimp)
  by (fastforce simp: valid_ep_q_def refill_prop_defs
                      active_sc_tcb_at_defs in_ep_q_def simple_obj_at_def
                      sufficient_refills_def refills_capacity_def
               split: option.splits)

lemma set_refills_valid_ep_q_not_in_ep_q:
  "\<lbrace>valid_ep_q and sc_not_in_ep_q sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ep_q\<rbrace>"
  by (wpsimp wp: set_refills_valid_ep_q)

lemma set_refills_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   scheduler_action s = switch_thread tcb_ptr \<longrightarrow>  (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_refills_def
  by (wpsimp wp: update_sched_context_weak_valid_sched_action)
     (clarsimp simp: active_sc_tcb_at_defs weak_valid_sched_action_def)

lemma set_refills_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_refills_weak_valid_sched_action
           simp: scheduler_act_not_def) fastforce

lemma set_refills_valid_sched_action:
  "\<lbrace>valid_sched_action and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   scheduler_action s = switch_thread tcb_ptr \<longrightarrow>  (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_refills_def
  by (wpsimp wp: update_sched_context_valid_sched_action)
     (clarsimp simp: active_sc_tcb_at_defs valid_sched_action_def weak_valid_sched_action_def)

lemma set_refills_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: scheduler_act_not_def obj_at_def
               wp: set_refills_valid_sched_action) fastforce

lemma set_refills_valid_blocked_except_set[wp]:
  "set_refills sc_ptr refills \<lbrace>valid_blocked_except_set S\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (auto simp: valid_blocked_except_set_def active_sc_tcb_at_defs st_tcb_at_kh_def)
  done

lemma set_refills_valid_sched:
  "\<lbrace>valid_sched
   and (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s
            \<longrightarrow> scheduler_action s = switch_thread tcb_ptr
            \<longrightarrow> MIN_BUDGET \<le> r_amount (hd refills)
                \<and> (r_time (hd refills)) \<le> (cur_time s) + kernelWCET_ticks)
    and (\<lambda>s. \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
           \<longrightarrow> in_ready_q t s
           \<longrightarrow> MIN_BUDGET \<le> r_amount (hd refills)
                \<and> (r_time (hd refills)) \<le> (cur_time s) + kernelWCET_ticks)
     and (\<lambda>s.  \<forall>t. bound_sc_tcb_at ((=) (Some sc_ptr)) t s
         \<longrightarrow> in_release_q t s
         \<longrightarrow> (\<forall>sc n. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow>
                                r_time (refill_hd sc) = r_time (hd refills)))\<rbrace>
  set_refills sc_ptr refills \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def
             wp: set_refills_valid_ready_qs set_refills_valid_release_q valid_idle_etcb_lift
                 set_refills_valid_sched_action)

lemma set_refills_valid_sched_not_in:
  "\<lbrace>valid_sched and sc_not_in_release_q sc_ptr and
     sc_not_in_ready_q sc_ptr and sc_scheduler_act_not sc_ptr\<rbrace>
    set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_refills_valid_release_q_not_in_release_q
                 set_refills_valid_ready_qs_not_queued
                 set_refills_valid_sched_action_act_not)

lemma set_refills_in_ep_q[wp]:
  "set_refills sc_ptr x1 \<lbrace>\<lambda>s. P (in_ep_q t s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp simp: Let_def)
  apply (erule subst[where P=P, rotated])
  apply (clarsimp simp: in_ep_q_def obj_at_def simple_obj_at_def)
  apply (rule iffI; clarsimp; rule_tac x=ptr in exI; clarsimp)
  done


context DetSchedSchedule_AI begin

lemma choose_thread_ct_not_queued:
  "\<lbrace> valid_ready_qs and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_ct_not_in_release_q:
  "\<lbrace> valid_release_q and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: switch_to_thread_ct_not_in_release_q guarded_switch_to_lift)

lemma choose_thread_ct_activatable:
  "\<lbrace> valid_ready_qs and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_ s::det_state.  st_tcb_at activatable (cur_thread s) s \<rbrace>"
  apply (wpsimp simp: choose_thread_def
                wp: guarded_switch_to_lift stit_activatable'[simplified ct_in_state_def]
                    stt_activatable[simplified ct_in_state_def])
  apply (fastforce dest!: next_thread_queued
                   simp: next_thread_def valid_ready_qs_def is_activatable_def in_cur_domain_def)
  done

lemma choose_thread_cur_dom_or_idle:
  "\<lbrace> valid_ready_qs \<rbrace>
   choose_thread
   \<lbrace>\<lambda>_ s::det_state. (in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s) \<rbrace>"
  apply (wpsimp simp: choose_thread_def
                wp: guarded_switch_to_lift)
      apply (rule hoare_disjI2) (* idle thread *)
      apply wp
     apply (rule hoare_disjI1) (* in current domain *)
     apply (wp guarded_switch_to_lift)+
  apply clarsimp
  apply (fastforce dest!: next_thread_queued split: option.splits
                   simp: etcb_at_def next_thread_def valid_ready_qs_def in_cur_domain_def)
  done

crunch sched_act[wp]: choose_thread "\<lambda>s::det_state. P (scheduler_action s)"
  (wp: guarded_switch_to_lift)

lemma valid_sched_action_from_choose_thread:
  "scheduler_action s = choose_new_thread \<Longrightarrow> valid_sched_action s"
  unfolding valid_sched_action_def by simp

crunch sched_act[wp]: tcb_sched_action "in_cur_domain t"

crunch ct_in_q[wp]: set_scheduler_action ct_in_q
  (simp: ct_in_q_def)

lemma ct_in_q_scheduler_action_update_id[simp]:
  "ct_in_q (scheduler_action_update f s) = ct_in_q s"
  by (simp add: ct_in_q_def active_sc_tcb_at_defs)

lemma set_scheduler_action_cnt_simple[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. simple_sched_action \<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_obvious[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action a \<lbrace>\<lambda>_ s. scheduler_action s = a\<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_cnt_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. scheduler_action s = switch_thread t \<and>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def wp: set_scheduler_action_valid_blocked_const)
     (clarsimp simp: not_queued_def in_ready_q_def)

lemma append_thread_queued:
  "\<lbrace>budget_sufficient thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. thread \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: etcb_at_def tcb_sched_append_def obj_at_def refill_prop_defs pred_tcb_at_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

(* having is_highest_prio match gets_wp makes it very hard to stop and drop imps etc. *)
definition
  "wrap_is_highest_prio cur_dom target_prio \<equiv> gets (is_highest_prio cur_dom target_prio)"

lemma schedule_choose_new_thread_valid_sched:
  "\<lbrace> valid_idle and valid_idle_etcb and valid_ready_qs and valid_release_q and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)
     and ct_in_q \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp_del: hoare_when_wp
                 wp: set_scheduler_action_rct_valid_sched_simple choose_thread_ct_not_queued
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action next_domain_valid_release_q
                      next_domain_valid_ready_qs next_domain_valid_blocked next_domain_ct_in_q)+
  done

lemma schedule_choose_new_thread_ct_not_queued:
  "\<lbrace> valid_idle and valid_ready_qs and valid_release_q and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp_del: hoare_when_wp
                 wp: choose_thread_ct_not_queued
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action next_domain_valid_release_q
                      next_domain_valid_ready_qs next_domain_valid_blocked next_domain_ct_in_q)+
  done

lemma schedule_choose_new_thread_ct_not_in_release_q:
  "\<lbrace> valid_idle and valid_ready_qs and valid_release_q and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp_del: hoare_when_wp
                 wp: choose_thread_ct_not_in_release_q
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action next_domain_valid_release_q
                      next_domain_valid_ready_qs next_domain_valid_blocked next_domain_ct_in_q)+
  done

crunches tcb_sched_action, tcb_release_enqueue
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: crunch_wps)

crunches set_scheduler_action, choose_thread
  for sc_not_in_release_q[wp]: "sc_not_in_release_q scp::det_state \<Rightarrow> _"
  and not_in_release_q[wp]: "not_in_release_q t::det_state \<Rightarrow> _"
  and sc_not_in_release_q_cur[wp]: "\<lambda>s::det_state. sc_not_in_release_q (cur_sc s) s"
    (simp: thread_get_def wp: crunch_wps)

lemma tcb_dequeue_sc_not_in_ready_q[wp]:
  "\<lbrace>sc_not_in_ready_q scp\<rbrace> tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>\<lambda>_. sc_not_in_ready_q scp\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)+
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_ready_qs_def
                  split: option.splits)
  done

lemma switch_to_thread_sc_not_in_ready_q[wp]:
  "\<lbrace>sc_not_in_ready_q scp\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::det_state. sc_not_in_ready_q scp s\<rbrace>"
  by (wpsimp simp: switch_to_thread_def get_tcb_obj_ref_def thread_get_def)

lemma tcb_dequeue_sc_not_in_ready_q_cur[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_ready_q (cur_sc s) s\<rbrace>
     tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>\<lambda>_ s. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)+
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_ready_qs_def
                  split: option.splits)
  done

lemma switch_to_thread_sc_not_in_ready_q_cur[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_ready_q (cur_sc s) s\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::det_state. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (wpsimp simp: switch_to_thread_def get_tcb_obj_ref_def thread_get_def)

crunches set_scheduler_action, switch_to_idle_thread, switch_to_thread
  for sc_not_in_ready_q[wp]: "sc_not_in_ready_q scp::det_state \<Rightarrow> _"
  and sc_not_in_ready_q_cur[wp]: "\<lambda>s::det_state. sc_not_in_ready_q (cur_sc s) s"
    (simp: thread_get_def tcb_sched_dequeue_def wp: crunch_wps)

lemma choose_thread_sc_not_in_ready_q[wp]:
  "\<lbrace> sc_not_in_ready_q scp \<rbrace> choose_thread \<lbrace>\<lambda>_. sc_not_in_ready_q scp :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_sc_not_in_ready_q_cur[wp]:
  "\<lbrace> \<lambda>s::det_state. sc_not_in_ready_q (cur_sc s) s \<rbrace> choose_thread \<lbrace>\<lambda>_ s. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: choose_thread_sc_not_in_ready_q guarded_switch_to_lift)

crunch valid_sched[wp]: cap_swap_for_delete, empty_slot "valid_sched :: det_state \<Rightarrow> _"
  (simp: unless_def wp: maybeM_inv ignore: set_object)

lemma update_sc_consumed_valid_sched:
  "\<lbrace>valid_sched\<rbrace> update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
      \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: get_object_wp simp: update_sched_context_def set_object_def)
  apply (clarsimp simp: valid_sched_def)
  apply (intro conjI)
      apply (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs
                             active_sc_tcb_at_defs st_tcb_at_kh_def
                      split: option.splits)
      apply solve_valid_release_q
     apply (clarsimp simp: valid_sched_action_def)
     apply (intro conjI)
       apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split obj_at_def pred_tcb_at_def)
      apply (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_if_split refill_prop_defs)
     apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs)
    apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs ct_in_cur_domain_def)
   apply (fastforce simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs split: option.splits)
  apply (clarsimp simp: valid_idle_etcb_def etcb_defs)
  done

crunch valid_sched[wp]: commit_domain_time "valid_sched :: det_state \<Rightarrow> _"
  (ignore: update_sched_context simp: Let_def set_refills_def
    wp: update_sched_context_valid_ready_qs get_sched_context_wp hoare_drop_imp)

(* valid_sched for refill_budget_check *)

lemma hd_last_length_2: "length ls = 2 \<Longrightarrow> [hd ls, last ls] = ls"
  apply (cases ls; clarsimp)
  by (case_tac list; clarsimp)


crunches refill_budget_check
for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: crunch_wps)

crunches commit_domain_time
  for valid_ready_qs[wp]: valid_ready_qs
  and valid_release_q[wp]: valid_release_q
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ko_at[wp]: "\<lambda>s. ko_at P t s"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
    (simp: crunch_simps wp: crunch_wps)

crunch ct_not_in_q[wp]: finalise_cap "ct_not_in_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp maybeM_inv
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

end

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and active_sc_tcb_at t and (\<lambda>s. t \<notin> set (release_queue s))
      and in_cur_domain t and simple_sched_action and budget_ready t and budget_sufficient t\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  by (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_def
                   weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
       split: scheduler_action.splits) fastforce+

lemma set_scheduler_action_swt_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
      and active_sc_tcb_at t and (\<lambda>s. t \<notin> set (release_queue s))
      and budget_sufficient t and budget_ready t
      and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_def
                   weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
       split: scheduler_action.splits)
  by (fastforce simp: valid_blocked_except_set_def)+

lemma set_scheduler_action_cnt_valid_blocked_except:
  "\<lbrace>\<lambda>s. valid_blocked_except target s
        \<and> (\<forall>t. scheduler_action s = switch_thread t \<longrightarrow> \<not> not_queued t s) \<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>rv. valid_blocked_except target::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  apply (fastforce simp: valid_blocked_except_def simple_sched_action_def
                   split: scheduler_action.splits)
  done

lemma enqueue_thread_not_not_queued:
  "\<lbrace>\<lambda>s. t = thread \<and>
      bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp 0 s \<and> is_refill_sufficient scp 0 s)) thread s \<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. \<not> not_queued t s \<rbrace>"
  apply (simp add: tcb_sched_action_def not_queued_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: pred_tcb_at_def tcb_sched_enqueue_def
                        is_refill_ready_def obj_at_def is_refill_sufficient_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

lemma reschedule_required_valid_blocked_except:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and (\<lambda>s. scheduler_action s \<noteq> resume_cur_thread)\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>rv. valid_blocked_except target :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    apply (clarsimp simp: pred_conj_def)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
   apply (rename_tac sched)
   apply (case_tac sched; clarsimp)
    apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except)
          apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except
                           tcb_sched_enqueue_valid_blocked_except_set_const
                           hoare_vcg_all_lift hoare_vcg_imp_lift enqueue_thread_not_not_queued)
         apply (wpsimp+)[4]
     apply (wpsimp simp: thread_get_def)
    apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def get_tcb_rev)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def is_refill_ready_def)
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except)
   apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def is_schedulable_opt_def
                         active_sc_tcb_at_def pred_tcb_at_def obj_at_def in_release_queue_def
                         get_tcb_rev)
  apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except)
  done

lemma set_scheduler_action_swt_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
    and active_sc_tcb_at t and budget_sufficient t and budget_ready t and in_cur_domain t
    and simple_sched_action and (\<lambda>s. \<not> in_release_queue t s)\<rbrace>
   set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wpsimp
  by (clarsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
     weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def not_in_release_q_def
     switch_in_cur_domain_def valid_blocked_def valid_blocked_except_def simple_sched_action_def
      split: scheduler_action.splits)

lemma possible_switch_to_valid_sched_strong:
  "\<lbrace>\<lambda>s. if (bound_sc_tcb_at bound target s \<and> not_in_release_q target s)
        then (valid_sched_except_blocked s \<and> valid_blocked_except target s
              \<and> st_tcb_at runnable target s \<and> (target \<noteq> idle_thread s)
              \<and> active_sc_tcb_at target s \<and> budget_ready target s \<and> budget_sufficient target s)
        else (valid_sched s) \<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (simp only: fun_app_def pred_tcb_at_eq_commute)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
   apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  apply (case_tac inq; clarsimp)
   apply wpsimp
   apply (fastforce simp: valid_sched_def valid_blocked_except_def not_in_release_q_def
                          in_release_queue_def valid_blocked_def)
  apply (wpsimp wp: set_scheduler_action_swt_valid_sched'
                    reschedule_required_valid_blocked_except)
  apply (subgoal_tac "bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) target s")
  apply (clarsimp simp: valid_sched_def)
  apply (safe)
  apply (clarsimp simp: not_cur_thread_def in_cur_domain_def obj_at_def ct_in_cur_domain_def etcb_defs)
  apply (fastforce simp: obj_at_def in_cur_domain_def etcb_defs pred_tcb_at_def has_budget_def)+
  done

crunch etcb_at[wp]: awaken "etcb_at P t"
  (wp: hoare_drop_imps mapM_x_wp')

crunches awaken
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  and valid_idle[wp]: valid_idle
  and in_cur_domain[wp]: "in_cur_domain t"
  (wp: hoare_drop_imps mapM_x_wp')

crunches possible_switch_to
  for valid_idle_etcb[wp]: "valid_idle_etcb"

lemma possible_switch_to_valid_ready_qs:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable target and
    ((bound_sc_tcb_at (\<lambda>sc. sc = None) target) or
     (active_sc_tcb_at target and budget_ready target and budget_sufficient target))\<rbrace>
    possible_switch_to target \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply wpsimp
  apply (fastforce simp: pred_tcb_at_eq_commute pred_tcb_at_def obj_at_def)
  done

lemma possible_switch_to_valid_ready_qs':
  "\<lbrace>valid_ready_qs \<comment> \<open>and st_tcb_at runnable target and active_sc_tcb_at target
    and budget_ready target and budget_sufficient target\<close>
      and (\<lambda>s. \<forall>tcb. ko_at (TCB tcb) target s \<and>
    tcb_domain tcb \<noteq> cur_domain s \<or>
    (tcb_domain tcb = cur_domain s \<and> scheduler_action s \<noteq> resume_cur_thread)
      \<longrightarrow> (runnable (tcb_state tcb) \<and> active_sc_tcb_at target s
             \<and> budget_ready target s \<and> budget_sufficient target s))\<rbrace>
    possible_switch_to target \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp], simp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp)
    apply (wpsimp+)[3]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: hoare_vcg_if_lift2)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def)
  done

lemma possible_switch_to_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  by wpsimp

lemma set_simple_ko_etcbs[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  by (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def a_type_def
           split: option.splits kernel_object.splits)

lemma set_simple_ko_active_sc_tcb_at[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (intro conjI; clarsimp elim!: rsubst [where P=P]; rule iffI)
  by (fastforce simp: active_sc_tcb_at_defs a_type_def partial_inv_def
         split: option.splits if_split_asm kernel_object.splits)+

lemma set_simple_ko_budget_ready[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: partial_inv_def obj_at_def)
  by (case_tac "f y";
         clarsimp simp: a_type_def pred_tcb_at_def obj_at_def is_refill_ready_def
              split: if_splits; intro conjI impI; clarsimp elim!: rsubst [where P=P];
         rule iffI; clarsimp; rule_tac x=scp in exI; clarsimp split: if_splits)

lemma set_simple_ko_budget_sufficient[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: partial_inv_def obj_at_def)
  by (case_tac "f y";
         clarsimp simp: a_type_def pred_tcb_at_def obj_at_def is_refill_sufficient_def
              split: if_splits; intro conjI impI; clarsimp elim!: rsubst [where P=P];
         rule iffI; clarsimp; rule_tac x=scp in exI; clarsimp split: if_splits)

lemma set_simple_ko_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps valid_ready_qs_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: hoare_vcg_conj_lift hoare_vcg_ball_lift get_object_wp
              simp: set_simple_ko_def set_object_def)
  by (intro conjI; clarsimp simp: partial_inv_def; solve_valid_release_q)

lemma set_simple_ko_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. switch_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps switch_in_cur_domain_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>_. ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps ct_in_cur_domain_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift hoare_drop_imps simp: set_simple_ko_def)

lemma set_simple_ko_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_sched_action:: det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps valid_sched_action_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_except_set_lift | simp add: set_simple_ko_def)+

lemma possible_switch_to_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc; wpsimp)
  done

lemma possible_switch_to_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and st_tcb_at runnable target
    and (bound_sc_tcb_at (\<lambda>sc. sc = None) target or
     (active_sc_tcb_at target and budget_ready target and budget_sufficient target))\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc)
     apply (wpsimp simp: set_scheduler_action_def | assumption)+
  by (fastforce simp: weak_valid_sched_action_def pred_tcb_at_def obj_at_def not_in_release_q_def)

lemma possible_switch_to_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc)
     by (wpsimp simp: set_scheduler_action_def|assumption)+

lemma possible_switch_to_activatable_ct[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace> possible_switch_to target \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma reschedule_required_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> reschedule_required \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (wpsimp simp: reschedule_required_def)

lemma possible_switch_to_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc)
  apply (wpsimp simp: set_scheduler_action_def|assumption)+
  by (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs obj_at_def
                  split: option.splits)

lemma possible_switch_to_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and st_tcb_at runnable target and active_sc_tcb_at target
    and budget_ready target and budget_sufficient target\<rbrace>
    possible_switch_to target \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
by (wpsimp simp: valid_sched_action_def)

crunches reply_unlink_sc,tcb_release_remove
  for etcb_at[wp]: "etcb_at P t"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches test_reschedule,tcb_release_remove
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches reply_unlink_tcb
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

lemma valid_sched_scheduler_act_not:
  "valid_sched s \<Longrightarrow> st_tcb_at ((=) k) y s \<Longrightarrow> ~ runnable k \<Longrightarrow> scheduler_act_not y s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        scheduler_act_not_def st_tcb_at_def obj_at_def)

lemma reply_unlink_tcb_valid_sched:
  "\<lbrace>valid_sched \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched gts_wp get_simple_ko_wp
                    set_simple_ko_valid_sched update_sk_obj_ref_lift)
  apply (intro conjI impI; clarsimp simp: reply_tcb_reply_at_def obj_at_def elim!: st_tcb_weakenE)
  apply (fastforce intro: valid_sched_scheduler_act_not)+
  done

lemma reply_unlink_tcb_valid_release_q:
  "\<lbrace>valid_release_q \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_release_q gts_wp get_simple_ko_wp
                    update_sk_obj_ref_lift)
  apply (intro conjI impI; clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_eq_commute elim!: st_tcb_weakenE)
  done

lemma reply_unlink_tcb_valid_ready_qs:
  "\<lbrace>valid_ready_qs \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_ready_qs gts_wp get_simple_ko_wp
                    update_sk_obj_ref_lift)
  apply (intro conjI impI; clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_eq_commute elim!: st_tcb_weakenE)
  done

lemma reply_unlink_tcb_valid_sched_action:
  "\<lbrace>valid_sched_action \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_act_not_valid_sched_action gts_wp get_simple_ko_wp
                    update_sk_obj_ref_lift)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        scheduler_act_not_def pred_tcb_at_def obj_at_def)
  apply (intro conjI impI; clarsimp elim!: st_tcb_weakenE)
  done

lemma reply_unlink_tcb_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_act_not_weak_valid_sched_action gts_wp get_simple_ko_wp
                    update_sk_obj_ref_lift)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        scheduler_act_not_def pred_tcb_at_def obj_at_def)
  apply (intro conjI impI; clarsimp elim!: st_tcb_weakenE)
  done

lemma reply_unlink_tcb_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: gts_wp get_simple_ko_wp update_sk_obj_ref_lift)
  done

lemma reply_unlink_tcb_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_release_q reply_unlink_tcb_valid_ready_qs
                    reply_unlink_tcb_valid_sched_action reply_unlink_tcb_ct_in_cur_domain)
  done

lemma reply_unlink_tcb_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_blocked_except_set S ::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_valid_blocked_except_set_const gts_wp get_simple_ko_wp update_sk_obj_ref_lift)
  done

lemma update_sched_context_etcbs_of[wp]:
  "update_sched_context p f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: etcbs_of'_non_tcb_update a_type_def obj_at_def)
  done

lemma update_sched_context_release_queue[wp]:
  "update_sched_context p f \<lbrace>\<lambda>s. P (release_queue s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  done

lemma get_tcb_NoneD: "get_tcb t s = None \<Longrightarrow> \<not> (\<exists>v. kheap s t = Some (TCB v))"
  apply (case_tac "kheap s t", simp_all add: get_tcb_def)
  apply (case_tac a, simp_all)
  done

lemma update_sc_replies_tcb_ready_time[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   update_sched_context p (sc_replies_update f)
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: tcb_ready_time_def obj_at_def split: option.splits)
  by (auto dest!: get_tcb_SomeD get_tcb_NoneD split: if_splits)

lemma update_sc_replies_valid_sched[wp]:
  " \<lbrace>valid_sched\<rbrace>
    update_sched_context scptr (sc_replies_update f)
    \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift
                 active_sc_tcb_at_update_sched_context_no_change
                 budget_ready_update_sched_context_no_change
                 budget_sufficient_update_sched_context_no_change
         simp: set_sc_obj_ref_def set_object_def)

lemma refills_remove1_valid_sched[wp]:
  " \<lbrace>valid_sched\<rbrace>
    set_sc_obj_ref sc_replies_update scptr new
    \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift
                 active_sc_tcb_at_update_sched_context_no_change
                 budget_ready_update_sched_context_no_change
                 budget_sufficient_update_sched_context_no_change
         simp: set_sc_obj_ref_def set_object_def)

crunches update_sk_obj_ref,get_sk_obj_ref
  for valid_sched[wp]: "valid_sched:: det_state \<Rightarrow> _"

lemma reply_unlink_sc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_unlink_sc scptr rptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  apply (wpsimp wp: hoare_vcg_imp_lift get_simple_ko_wp)
  done

lemma reply_unlink_tcb_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
   reply_unlink_tcb tptr rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: set_thread_state_valid_blocked_const gts_wp get_simple_ko_wp
           simp: update_sk_obj_ref_def)

lemma set_scheduler_action_swt_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except_set (insert t X) and st_tcb_at runnable t
     and budget_ready t and budget_sufficient t
     and active_sc_tcb_at t and in_cur_domain t and simple_sched_action and (\<lambda>s. \<not> in_release_queue t s)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_ s:: det_state. valid_sched_except_blocked s \<and> valid_blocked_except_set X s \<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wpsimp
  by (force simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
                  weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def
                  not_in_release_q_def switch_in_cur_domain_def valid_blocked_def
                  valid_blocked_except_def simple_sched_action_def
           split: scheduler_action.splits)

lemma valid_nftn_qD1:
  "valid_ntfn_q s \<Longrightarrow>
   ko_at (Notification ntfn) ntfnptr s \<Longrightarrow>
   ntfn_obj ntfn = WaitingNtfn WNlist \<Longrightarrow>
   t \<in> set WNlist \<Longrightarrow>
   has_budget t s"
  apply (clarsimp simp: valid_ntfn_q_def obj_at_def has_budget_def simple_obj_at_def)
  apply (drule_tac x = ntfnptr in spec)
  apply (fastforce simp: ntfn_queue_def)
  done

lemma valid_nftn_qD2:
  "valid_ntfn_q s \<Longrightarrow>
   ko_at (Notification ntfn) ntfnptr s \<Longrightarrow>
   ntfn_obj ntfn = WaitingNtfn WNlist \<Longrightarrow>
   t \<in> set WNlist \<Longrightarrow>
   not_cur_thread t s"
  apply (clarsimp simp: valid_ntfn_q_def obj_at_def has_budget_def not_cur_thread_def)
  apply (drule_tac x = ntfnptr in spec)
  apply (fastforce simp: ntfn_queue_def)
  done

lemma set_thread_state_has_budget[wp]:
  "\<lbrace>has_budget x\<rbrace>
   set_thread_state tcbptr ts
   \<lbrace>\<lambda>rv. has_budget x :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: has_budget_equiv2 wp: hoare_vcg_disj_lift)

lemma thread_set_has_budget[wp]:
  assumes "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  shows "thread_set f tptr \<lbrace>has_budget x :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: has_budget_equiv2 assms
               wp: hoare_vcg_disj_lift thread_set_no_change_tcb_pred_gen
                   active_sc_tcb_at_thread_set_no_change
                   budget_sufficient_thread_set_no_change
                   budget_ready_thread_set_no_change)

lemma possible_switch_to_valid_sched_weak:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and (\<lambda>s. target \<noteq> idle_thread s)
    and (\<lambda>s. bound_sc_tcb_at bound target s
       \<longrightarrow> st_tcb_at runnable target s \<and> active_sc_tcb_at target s
           \<and> budget_ready target s \<and> budget_sufficient target s)\<rbrace>
     possible_switch_to target
    \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wp possible_switch_to_valid_sched_strong)
  apply (clarsimp simp: valid_sched_def)
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
  apply (case_tac "t=target", simp)
    apply (clarsimp simp: active_sc_tcb_at_defs)
  by fastforce

lemma possible_switch_to_valid_sched_except_blocked_inc:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except_set (insert target S)
     and (\<lambda>s. target \<noteq> idle_thread s) and K (target \<notin> S)
     and (\<lambda>s. bound_sc_tcb_at bound target s \<and> not_in_release_q target s
          \<longrightarrow> st_tcb_at runnable target s \<and> active_sc_tcb_at target s
              \<and> budget_ready target s \<and> budget_sufficient target s)\<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv s:: det_state. valid_blocked_except_set S s\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: valid_blocked_except_set_def)
   apply (case_tac "t=target"; fastforce simp: active_sc_tcb_at_defs)
  apply (case_tac inq; clarsimp)
   apply wpsimp
   apply (clarsimp simp: valid_blocked_except_set_def)
   apply (drule_tac x=t in spec, clarsimp, case_tac "t\<in>S"; clarsimp simp: in_release_queue_def not_in_release_q_def)
   apply (case_tac "t=target"; clarsimp)
  apply (wpsimp simp: bind_assoc
      wp: set_scheduler_action_valid_blocked_except_set
      tcb_sched_enqueue_valid_blocked_except_set
      reschedule_required_valid_blocked
      set_scheduler_action_swt_valid_sched_except_blocked[where X="S", simplified]
      wp_del: set_scheduler_action_valid_ready_qs
     | rule_tac Q="\<lambda>_. valid_sched_except_blocked and valid_blocked_except_set S"
          in hoare_strengthen_post)+
  by (fastforce simp: etcb_defs in_cur_domain_def obj_at_def pred_tcb_at_def split: option.splits)


crunches reply_unlink_tcb
for not_cur_thread[wp]: "not_cur_thread t"
and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
  (wp: crunch_wps)

definition valid_ep_thread_simple_2 where (* valid_ep_thread without thread_state condition *)
  "valid_ep_thread_simple_2 t ct it curtime kh =
       (t \<noteq> ct \<and> t \<noteq> it \<and>
         (bound_sc_tcb_at_kh ((=) None) t kh \<or>
        active_sc_tcb_at_kh t kh \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh))"

abbreviation valid_ep_thread_simple :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_ep_thread_simple t s \<equiv>
     valid_ep_thread_simple_2 t (cur_thread s) (idle_thread s) (cur_time s) (kheap s)"

lemma set_simple_ko_valid_ep_thread_simple[wp]:
  "\<lbrace>\<lambda>s. valid_ep_thread_simple t s\<rbrace>
       set_simple_ko C ptr ep \<lbrace>\<lambda>rv s::det_state. valid_ep_thread_simple t s\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: partial_inv_def obj_at_def)
  apply (unfold valid_ep_thread_simple_2_def)
  apply (elim conjE disjE; simp)
   apply (intro impI conjI; rule disjI1,
      clarsimp simp: bound_sc_tcb_at_kh_if_split pred_tcb_at_def obj_at_def)
  by (intro impI conjI; rule disjI2,
      clarsimp simp: active_sc_tcb_at_kh_if_split active_sc_tcb_at_defs refill_prop_defs
               split: option.splits,
      intro conjI impI; fastforce?)

crunches possible_switch_to,set_thread_state_act
  for valid_ep_thread_simple[wp]: "valid_ep_thread_simple t::det_state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

lemma set_thread_state_valid_ep_thread_simple[wp]:
  "\<lbrace>\<lambda>s. valid_ep_thread_simple t s\<rbrace>
   set_thread_state t' st
   \<lbrace>\<lambda>rv s::det_state. valid_ep_thread_simple t s\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  apply (simp add: valid_ep_thread_simple_2_def)
  apply (elim conjE disjE)
   apply (clarsimp simp: active_sc_tcb_at_defs dest!: get_tcb_SomeD)
  apply (rule disjI2)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs
               dest!: get_tcb_SomeD split: option.splits)

crunches restart_thread_if_no_fault, reply_unlink_tcb
  for valid_ep_thread_simple[wp]: "valid_ep_thread_simple t::det_state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

lemma valid_ep_q_imp_valid_ep_thread_simple:
  "\<lbrakk>valid_ep_q s; t \<in> set queue; queue = ep_queue ep; ko_at (Endpoint ep) epptr s\<rbrakk>
       \<Longrightarrow> valid_ep_thread_simple t s"
  apply (clarsimp simp: valid_ep_q_def)
  by (drule_tac x=epptr in spec, clarsimp simp: obj_at_def valid_ep_thread_simple_2_def)

lemma reply_unlink_tcb_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t'\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. scheduler_act_not t'\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: gts_wp get_simple_ko_wp)

lemma restart_thread_if_no_fault_valid_sched:
  "\<lbrace>valid_ep_thread_simple t and
    st_tcb_at (not runnable) t and
    valid_sched\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  apply (simp add: restart_thread_if_no_fault_def)
  apply (wpsimp wp: set_thread_state_runnable_valid_ready_qs hoare_vcg_disj_lift
                    set_thread_state_runnable_valid_release_q
                    set_thread_state_runnable_valid_sched_action
                    set_thread_state_valid_blocked_except_set_const sts_st_tcb_at'
                    possible_switch_to_valid_sched_weak[simplified has_budget_equiv2]
                    set_thread_state_not_runnable_valid_sched thread_get_wp
                    hoare_vcg_imp_lift')+
  by (auto simp: valid_sched_def valid_ep_thread_simple_2_def
                 not_cur_thread_def pred_tcb_at_def obj_at_def pred_neg_def
         intro!: valid_sched_scheduler_act_not)

lemma st_tcb_at_inactive_runnable:
  "st_tcb_at ((=) Inactive) t s \<Longrightarrow> st_tcb_at (not runnable) t s "
  by (clarsimp elim!: st_tcb_weakenE simp: pred_neg_def)

lemma reply_unlink_tcb_not_runnable[wp]:
  "\<lbrace>\<top>\<rbrace>
     reply_unlink_tcb t r
   \<lbrace>\<lambda>rv. st_tcb_at (not runnable) t\<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_inactive
         | strengthen st_tcb_at_inactive_runnable)+

lemma cancel_all_ipc_valid_sched_helper0:
  "\<lbrace>valid_ep_thread_simple t and scheduler_act_not t and
    st_tcb_at (not runnable) t and
    valid_sched\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        y <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac st; clarsimp)
         defer 4
         apply (wpsimp wp: restart_thread_if_no_fault_valid_sched
                           reply_unlink_tcb_valid_sched)+
  done

lemma cancel_all_ipc_valid_sched_helper1:
  "\<lbrace>valid_ep_thread_simple t'\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        _ <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
  \<lbrace>\<lambda>_. valid_ep_thread_simple t'::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp hoare_drop_imps)

(* strong in case of tcb_domain t = tcb_domain target *)
lemma possible_switch_to_sched_act_not[wp]:
  "\<lbrace>K(t \<noteq> target) and scheduler_act_not t\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def thread_get_def
                   set_scheduler_action_def tcb_sched_action_def get_tcb_obj_ref_def
              split del: if_split
        | wp | wpc)+
  apply (clarsimp simp: etcb_at_def scheduler_act_not_def split: option.splits)
  done

crunches restart_thread_if_no_fault
  for scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: crunch_wps)

lemma cancel_all_ipc_valid_sched_helper2:
  "\<lbrace>\<lambda>s. scheduler_act_not t' s \<and> t' \<noteq> t\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        _ <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
  \<lbrace>\<lambda>_. scheduler_act_not t'::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp)

lemma cancel_all_ipc_valid_sched_helper3:
  "\<lbrace>\<lambda>s. st_tcb_at (not runnable) t' s
        \<and> t' \<noteq> t\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        _ <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
  \<lbrace>\<lambda>_. st_tcb_at (not runnable) t' ::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: restart_thread_if_no_fault_other reply_unlink_tcb_st_tcb_at gts_wp)

lemma cancel_all_ipc_valid_sched_helper:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. valid_ep_thread_simple t s \<and>
                       scheduler_act_not t s \<and>
                       st_tcb_at (not runnable) t s)
    and valid_sched and K (distinct queue)\<rbrace>
     mapM_x (\<lambda>t. do st <- get_thread_state t;
                    reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro | _ \<Rightarrow> return None;
                    _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb t (the reply_opt));
                    restart_thread_if_no_fault t
                 od) queue
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_mapM_x_scheme)
  by (wpsimp wp: cancel_all_ipc_valid_sched_helper0 cancel_all_ipc_valid_sched_helper1
                 cancel_all_ipc_valid_sched_helper2 cancel_all_ipc_valid_sched_helper3)+

lemma cancel_all_ipc_valid_sched:
  "\<lbrace>valid_objs and valid_sched and valid_ep_q and simple_sched_action
    and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
     cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp simp: get_ep_queue_def;
          wpsimp wp: hoare_vcg_ball_lift cancel_all_ipc_valid_sched_helper
                     reschedule_valid_sched_const)
   by (auto simp: obj_at_def is_ep valid_objs_ko_at valid_obj_def valid_ep_def
                  ep_queued_st_tcb_at pred_neg_def
           dest!: valid_ep_q_imp_valid_ep_thread_simple)

lemma cancel_all_signals_valid_sched_helper0:
  "\<lbrace>valid_ep_thread_simple t and valid_sched\<rbrace>
      ( do y <- set_thread_state t Restart;
           possible_switch_to t
        od)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  apply (wpsimp simp: has_budget_equiv2
                  wp: set_thread_state_break_valid_sched hoare_vcg_imp_lift
                      possible_switch_to_valid_sched_weak sts_st_tcb_at')
  by (clarsimp simp: valid_sched_def valid_ep_thread_simple_2_def not_cur_thread_def)

lemma cancel_all_signals_valid_sched_helper1:
  "\<lbrace>valid_ep_thread_simple t'\<rbrace>
      ( do y <- set_thread_state t Restart;
           possible_switch_to t
        od)
  \<lbrace>\<lambda>_. valid_ep_thread_simple t'::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp)

lemma cancel_all_signals_valid_sched_helper:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. valid_ep_thread_simple t s) and valid_sched and K (distinct queue)\<rbrace>
       mapM_x (\<lambda>t.
             do y <- set_thread_state t Restart;
                possible_switch_to t
             od) queue
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_mapM_x_scheme)
  by (wpsimp wp: cancel_all_signals_valid_sched_helper1 cancel_all_signals_valid_sched_helper0)+

lemma valid_ntfn_q_imp_valid_ep_thread_simple:
  "\<lbrakk>t \<in> set queue; ntfn_obj ntfn = WaitingNtfn queue; ko_at (Notification ntfn) ptr s; valid_ntfn_q s\<rbrakk>
       \<Longrightarrow> valid_ep_thread_simple t s"
  apply (clarsimp simp: valid_ntfn_q_def)
  by (drule_tac x=ptr in spec, clarsimp simp: obj_at_def valid_ep_thread_simple_2_def ntfn_queue_def)

lemma cancel_all_signals_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_ntfn_q and valid_objs\<rbrace>
     cancel_all_signals ntfnptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    defer 2
    apply (wpsimp+)[2]
  apply (rename_tac queue)
  apply (wpsimp wp: cancel_all_signals_valid_sched_helper hoare_vcg_ball_lift
                    reschedule_valid_sched_const)
  by (auto simp: valid_obj_def valid_ntfn_def
                 valid_ntfn_q_imp_valid_ep_thread_simple
          dest!: valid_objs_ko_at )

crunches thread_set
for ready_queues[wp]:  "\<lambda>s. P (ready_queues s)"
and release_queue'[wp]:  "\<lambda>s. P (release_queue s)"
and cur_domain'[wp]:  "\<lambda>s. P (cur_domain s)"

lemma thread_set_etcbs:
  "\<lbrakk>\<And>x. tcb_priority (f x) = tcb_priority x; \<And>x. tcb_domain (f x) = tcb_domain x\<rbrakk> \<Longrightarrow>
  thread_set f tptr \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  by (auto elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp: etcbs_of'_def)

lemma thread_set_active_sc_tcb_at:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
  thread_set f tptr \<lbrace>active_sc_tcb_at t\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto dest!: get_tcb_SomeD
       simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  by (rule_tac x=scp in exI, fastforce)+

lemma thread_set_valid_ready_qs:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_priority (f x) = tcb_priority x;
    \<And>x. tcb_domain (f x) = tcb_domain x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
    \<lbrace>valid_ready_qs\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (rule valid_ready_qs_lift;
      wpsimp wp: thread_set_no_change_tcb_state thread_set_etcbs thread_set_active_sc_tcb_at
                 budget_ready_thread_set_no_change budget_sufficient_thread_set_no_change)+

lemma thread_set_valid_release_q:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x;
    \<And>x. tcb_domain (f x) = tcb_domain x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
    \<lbrace>valid_release_q\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (rule valid_release_q_lift;
      wpsimp wp: thread_set_no_change_tcb_state thread_set_active_sc_tcb_at)+

lemma thread_set_weak_valid_sched_action:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: weak_valid_sched_action_lift thread_set_no_change_tcb_state
                 active_sc_tcb_at_thread_set_no_change hoare_drop_imps
                 budget_sufficient_thread_set_no_change budget_ready_thread_set_no_change
             simp: thread_set_def)

lemma thread_set_not_state_valid_sched:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   (\<And>x. tcb_priority (f x) = tcb_priority x) \<Longrightarrow>
   (\<And>x. tcb_domain (f x) = tcb_domain x) \<Longrightarrow>
   \<lbrace>valid_sched\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift active_sc_tcb_at_thread_set_no_change
         thread_set_no_change_tcb_state thread_set_etcbs
         budget_ready_thread_set_no_change budget_sufficient_thread_set_no_change |
      simp add: thread_set_def)+

lemma unbind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_notification ntfnptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptra, simp add: maybeM_def, wp, simp)
  apply (wpsimp wp: maybeM_inv set_bound_notification_valid_sched simp: update_sk_obj_ref_def)
  done

crunches set_sc_obj_ref
for cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

lemma tcb_release_remove_not_in_release_q':
  "tcb_release_remove thread \<lbrace>not_in_release_q t \<rbrace>"
  by (wpsimp simp: tcb_release_remove_def not_in_release_q_def tcb_sched_dequeue_def)

crunches test_reschedule
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
and not_in_release_q[wp]: "not_in_release_q t::det_state \<Rightarrow> _"
and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
and valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and test_sc_refill_max[wp]: "\<lambda>s. P (test_sc_refill_max p s)"
and is_refill_ready[wp]: "(\<lambda>s. Q (is_refill_ready p u s))::det_state \<Rightarrow> _"
and is_refill_sufficient[wp]: "is_refill_sufficient p u::det_state \<Rightarrow> _"
and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: hoare_drop_imps hoare_vcg_if_lift2 reschedule_valid_sched_const)

crunches tcb_release_remove
for cur_time[wp]: "\<lambda>s. P (cur_time s)"
and test_sc_refill_max[wp]: "test_sc_refill_max p::det_state \<Rightarrow> _"
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

crunches test_reschedule,tcb_release_remove
for not_queued[wp]: "not_queued t"
  (wp: hoare_vcg_if_lift2)

lemma sc_tcb_sc_at_set_tcb_queue_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> tp \<notin> set queue) t s\<rbrace>
       set_tcb_queue d prio queue
        \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  apply (wpsimp simp: set_tcb_queue_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def not_queued_def)

lemma sc_tcb_sc_at_set_scheduler_actione_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace>
       set_scheduler_action f
        \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  by (wpsimp simp: set_scheduler_action_def)

lemma sc_tcb_sc_at_tcb_sched_enqueue_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> tp \<noteq> t') t s\<rbrace>
       tcb_sched_action tcb_sched_enqueue t'
        \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  by (fastforce simp: sc_tcb_sc_at_def obj_at_def tcb_sched_enqueue_def)

lemma sc_tcb_sc_at_reschedule_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> scheduler_act_not tp s) t s\<rbrace>
       reschedule_required
        \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  apply (clarsimp simp: reschedule_required_def)
  apply (wpsimp simp: thread_get_def
    wp: is_schedulable_wp sc_tcb_sc_at_tcb_sched_enqueue_not_queued
        sc_tcb_sc_at_set_scheduler_actione_not_queued)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def not_queued_def scheduler_act_not_def)

lemma sc_tcb_sc_at_test_reschedule_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> scheduler_act_not tp s) t s\<rbrace>
       test_reschedule tptr
        \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  apply (clarsimp simp: test_reschedule_def)
  apply (wpsimp simp: test_reschedule_def wp: sc_tcb_sc_at_reschedule_not_queued)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def not_queued_def)

(* sched_context_donate *)
lemma sched_context_donate_valid_ready_qs_helper:
  "\<lbrace>valid_ready_qs and not_queued tptr\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued)
   apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
      wp: get_object_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def valid_ready_qs_def is_etcb_at'_def etcbs_of'_def etcb_at'_def)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
      refill_sufficient_kh_def refill_ready_kh_def
                is_refill_sufficient_def is_refill_ready_def
               dest!: get_tcb_SomeD split: option.splits)

lemma sched_context_donate_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and not_queued tptr and scheduler_act_not tptr\<rbrace>
        sched_context_donate scptr tptr \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def assert_opt_def)
  by (wpsimp wp: sched_context_donate_valid_ready_qs_helper
      set_tcb_sched_context_valid_ready_qs_not_queued tcb_dequeue_not_queued
      tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued_gen
      simp: get_sc_obj_ref_def)

lemma valid_and_no_sc_imp_not_in_release_q:
  "\<lbrakk>valid_release_q s; bound_sc_tcb_at ((=) None) tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  apply (clarsimp simp: valid_release_q_def active_sc_tcb_at_defs not_in_release_q_def)
  by (drule_tac x=tptr in bspec, simp) fastforce

lemma sched_context_donate_valid_release_q_helper:
  "\<lbrace>valid_release_q and not_in_release_q tptr\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_release_q_not_queued)
   by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
      wp: get_object_wp) solve_valid_release_q

lemma sched_context_donate_valid_release_q:
  "\<lbrace>valid_release_q and bound_sc_tcb_at ((=) None) tptr\<rbrace>
        sched_context_donate scptr tptr \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (rule_tac Q="valid_release_q and not_in_release_q tptr" in hoare_weaken_pre[rotated])
   apply (clarsimp dest!: valid_and_no_sc_imp_not_in_release_q[rotated])
  apply (clarsimp simp: sched_context_donate_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac from_opt; clarsimp)
   apply (wpsimp wp: sched_context_donate_valid_release_q_helper)
  by (wpsimp wp: sched_context_donate_valid_release_q_helper
                    set_tcb_sched_context_valid_release_q_not_queued)
     (clarsimp simp: not_in_release_q_def)


lemma sched_context_donate_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (wpsimp simp: wp: get_sched_context_wp tcb_dequeue_not_queued_gen set_tcb_obj_ref_not_queued)
  done

crunches set_sc_obj_ref
for valid_sched: "valid_sched::det_state \<Rightarrow> _"
and valid_ready_qs: "valid_ready_qs::det_state \<Rightarrow> _"
and valid_release_q: "valid_release_q::det_state \<Rightarrow> _"
and ct_in_cur_domain: "ct_in_cur_domain::det_state \<Rightarrow> _"
and valid_sched_action: "valid_sched_action::det_state \<Rightarrow> _"
and weak_valid_sched_action: "weak_valid_sched_action::det_state \<Rightarrow> _"
and switch_in_cur_domain[wp]: "switch_in_cur_domain::det_state \<Rightarrow> _"
and cur_activatable[wp]: "\<lambda>s::det_state. is_activatable (cur_thread s) s"

lemma set_sc_tcb_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs refill_prop_defs st_tcb_at_kh_def)

lemma set_sc_ntfn_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs refill_prop_defs st_tcb_at_kh_def)

lemma set_sc_tcb_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by(wpsimp simp: valid_sched_action_def)

lemma set_sc_ntfn_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by(wpsimp simp: valid_sched_action_def)

crunches thread_set, test_reschedule
for sched_act_not[wp]: "scheduler_act_not t"
  (wp: crunch_wps simp: crunch_simps)

declare test_reschedule_sched_act_not [wp del]

lemma sched_context_donate_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  by (wpsimp wp: hoare_vcg_if_lift2 set_tcb_sched_context_valid_sched_action_act_not
       get_sched_context_wp test_reschedule_sched_act_not)

crunches sched_context_donate
for ct_in_cur_domain[wp]: "ct_in_cur_domain :: det_state \<Rightarrow> _"
  (wp: maybeM_wp hoare_drop_imp maybeM_wp hoare_vcg_if_lift2 ignore: sched_context_donate)


lemma set_tcb_sched_context_is_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (wpsimp simp: is_activatable_def set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma set_sc_tcb_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: valid_blocked_def active_sc_tcb_at_defs st_tcb_at_kh_def)

lemma set_sc_ntfn_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: valid_blocked_def active_sc_tcb_at_defs st_tcb_at_kh_def)

crunches set_sc_obj_ref
  for valid_blocked: "valid_blocked::det_state \<Rightarrow> _"

lemma set_sc_tcb_sched_context_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_sc_obj_ref_valid_sched)
  by (intro conjI impI allI;
      (fastforce simp: valid_sched_def valid_ready_qs_def valid_release_q_def
                       valid_sched_action_def weak_valid_sched_action_def
                       sufficient_refills_def refills_capacity_def
                       active_sc_tcb_at_defs in_queue_2_def refill_prop_defs)?)

lemma set_sc_ntfn_sched_context_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_sc_obj_ref_valid_sched)
  by (intro conjI impI allI;
      (fastforce simp: valid_sched_def valid_ready_qs_def valid_release_q_def
                       valid_sched_action_def weak_valid_sched_action_def
                       sufficient_refills_def refills_capacity_def
                       active_sc_tcb_at_defs in_queue_2_def refill_prop_defs)?)

lemma set_sc_refill_max_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. \<forall>tptr. scheduler_action s = switch_thread tptr \<longrightarrow>
          bound_sc_tcb_at (\<lambda>x. x = Some ref) tptr s \<longrightarrow> 0 < j)\<rbrace>
     set_sc_obj_ref sc_refill_max_update ref j
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_wp)
  apply (clarsimp simp: valid_sched_action_def)
  apply (intro conjI)
    apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: weak_valid_sched_action_def)
   apply (intro conjI)
    apply (clarsimp simp: st_tcb_at_kh_def active_sc_tcb_at_defs)
    apply (fastforce simp: refill_prop_defs active_sc_tcb_at_defs)+
  by (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs)

lemma set_sc_refill_max_valid_sched[wp]:
  "\<lbrace>valid_sched and
    (\<lambda>s. \<forall>t. bound_sc_tcb_at (\<lambda>x. x = Some ref) t s \<longrightarrow>
             (not_queued t s \<and> not_in_release_q t s \<and> scheduler_action s \<noteq> switch_thread t))\<rbrace>
   set_sc_obj_ref sc_refill_max_update ref 0
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_sched_def
                  wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q valid_idle_etcb_lift
                      set_sc_obj_ref_ct_in_cur_domain set_sc_obj_ref_valid_blocked set_sc_obj_ref_valid_sched_action)
  by (fastforce simp: pred_tcb_at_def obj_at_def in_queue_2_def not_queued_def not_in_release_q_def)

lemma tcb_release_remove_valid_sched_not_runnable:
  "\<lbrace>valid_sched and (\<lambda>s. \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s))\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_release_remove_valid_blocked_const)+

lemma tcb_release_remove_valid_sched_except_blocked:
  "\<lbrace>valid_sched\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_release_remove_valid_blocked_const)+

crunches set_mrs,set_message_info,set_consumed,reply_unlink_sc
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain'[wp]: "\<lambda>s. P (cur_domain s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM crunch_simps wp: mapM_wp' hoare_drop_imp crunch_wps)

lemma set_mrs_etcbs[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_mrs_def store_word_offs_def
  supply if_split [split del]
  by (wpsimp simp: zipWithM_x_mapM wp: mapM_wp' set_object_wp)

crunches set_message_info,set_consumed,reply_unlink_sc
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: crunch_wps)

lemma as_user_active_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> as_user t' m \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wp as_user_wp_thread_set_helper active_sc_tcb_at_thread_set_no_change
      | simp add: thread_set_def)+

lemma as_user_budget_ready [wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> as_user t' m \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  by (wp as_user_wp_thread_set_helper budget_ready_thread_set_no_change
      | simp add: thread_set_def)+

lemma as_user_budget_sufficient [wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> as_user t' m \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  by (wp as_user_wp_thread_set_helper budget_sufficient_thread_set_no_change
      | simp add: thread_set_def)+

lemma as_user_bound_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (bound_sc_tcb_at Q t s)\<rbrace> as_user t' m \<lbrace>\<lambda>rv s. P (bound_sc_tcb_at Q t s)\<rbrace>"
  by (wp as_user_pred_tcb_at)

crunches set_message_info
  for active_sc_tcb_at[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
  and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
  and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"

lemma set_mrs_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: wp: valid_sched_lift)

lemma set_mrs_valid_sched_except_blocked[wp]:
  "set_mrs param_a param_b param_c \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>valid_idle_etcb::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  "set_mrs param_a param_b param_c \<lbrace>ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: wp: valid_sched_except_blocked_lift weak_valid_sched_action_lift)+

lemma set_mrs_scheduler_act_sane[wp]:
  "set_mrs param_a param_b param_c \<lbrace>scheduler_act_sane::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_weaken_pre, wps, wpsimp, simp)

lemma set_mrs_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
      set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: wp: valid_blocked_except_set_lift)

lemma set_mrs_ko_at_Endpoint[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
     set_mrs param_a param_b param_c
   \<lbrace>\<lambda>_ s :: det_state. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  apply (wpsimp simp: set_mrs_def wp: zipWithM_x_inv' set_object_wp)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

lemma set_mrs_valid_ep_q[wp]:
  "\<lbrace>valid_ep_q\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: wp: valid_ep_q_lift hoare_vcg_disj_lift)

(* FIXME maybe move *)
lemma as_user_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   as_user tptr f
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

(* FIXME maybe move *)
lemma set_message_info_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   set_message_info thread info
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  by (wpsimp simp: set_message_info_def set_object_def wp:  get_object_wp
                split_del: if_split)

(* FIXME maybe move *)
crunches set_message_info, as_user
  for tcb_ready_time[wp]: "\<lambda>s. P (tcb_ready_time t s) (tcb_ready_time t' s)"
    (rule: release_queue_cmp_lift)

lemma set_message_info_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_message_info thread info \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp:  wp: valid_sched_lift)

crunches store_word_offs
  for active_sc_tcb_at[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
  (simp: zipWithM_x_mapM wp: dmo_active_sc_tcb_at mapM_wp' active_sc_tcb_at_set_object_no_change_sc ignore: update_sched_context)

lemma reply_remove_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and valid_objs::det_state \<Rightarrow> _\<rbrace>
     reply_remove tptr rptr
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp simp: assert_opt_def)
  apply (wpsimp wp: gbn_wp static_imp_wp hoare_vcg_if_lift2)
  apply (auto simp: obj_at_def valid_obj_def valid_reply_def is_tcb)
  done

lemma set_simple_ko_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace> set_simple_ko C f new \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  by (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)

lemma set_sc_obj_ref_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace> set_sc_obj_ref f p new \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)

crunches test_reschedule
  for valid_blocked[wp]: "valid_blocked :: det_state \<Rightarrow> _"
    (wp: hoare_vcg_if_lift2)

crunches reply_remove_tcb,thread_set
for not_queued[wp]: "not_queued t :: det_state \<Rightarrow> _"
and not_in_release_q[wp]:  "not_in_release_q t :: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps hoare_vcg_if_lift2 tcb_release_remove_not_in_release_q')

lemma test_reschedule_no_action:
  "\<lbrace>\<top>\<rbrace> test_reschedule t \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (clarsimp simp: test_reschedule_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp; wpsimp wp: reschedule_required_scheduler_act_not)
  by (clarsimp simp: scheduler_act_not_def)

crunches test_reschedule,tcb_release_remove
for active_sc_tcb_at[wp]: "active_sc_tcb_at t"
and obj_at[wp]: "obj_at P p"
  (wp: crunch_wps ignore: set_object )

lemma set_tcb_queue_get_tcb[wp]:
 "\<lbrace>\<lambda>s. get_tcb t s = x\<rbrace> set_tcb_queue param_a param_b param_c \<lbrace>\<lambda>_ s. get_tcb t s = x\<rbrace> "
  by (wpsimp simp: set_tcb_queue_def get_tcb_def)

crunches test_reschedule,tcb_release_remove
for get_tcb[wp]: "\<lambda>s. get_tcb t s = x"
  (wp: hoare_drop_imp)

lemma sched_context_donate_active_sc_tcb_at_neq:
  "\<lbrace>active_sc_tcb_at t and K (t \<noteq> tcb_ptr) and sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) sc_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp simp: set_object_def update_sched_context_def
                wp: get_object_wp set_tcb_sc_update_active_sc_tcb_at_neq)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma set_sc_tcb_st_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace> set_sc_obj_ref sc_tcb_update sc tcb \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_sc_obj_ref_def set_object_def)
  apply wp
  done

crunches test_reschedule
for weak_valid_sched_action[wp]: weak_valid_sched_action
  (wp: hoare_vcg_if_lift2)

lemma tcb_release_remove_valid_blocked_except2:
  "\<lbrace>valid_blocked_except thread\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def valid_blocked_except_def valid_blocked_def
                      tcb_sched_dequeue_def not_in_release_q_def)

lemma test_reschedule_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace>
     test_reschedule tptr \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  by (wpsimp simp: test_reschedule_def wp: reschedule_required_not_queued)

crunches tcb_release_remove
for ct_not_queued[wp]: ct_not_queued
and scheduler_act_sane[wp]: scheduler_act_sane
and ct_not_in_release_q[wp]: ct_not_in_release_q
  (simp: not_in_release_q_def tcb_sched_dequeue_def)

lemma test_reschedule_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace> test_reschedule tptr \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  by (wpsimp simp: test_reschedule_def wp: reschedule_required_not_in_release_q)

lemma sched_context_donate_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> sched_context_donate sc_ptr tptr \<lbrace>\<lambda>_. ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def update_sched_context_def
       tcb_sched_action_def get_sc_obj_ref_def thread_get_def set_object_def
          wp: hoare_drop_imp hoare_vcg_if_lift2 get_sched_context_wp)
  apply (clarsimp simp: etcb_at_def not_queued_def tcb_sched_dequeue_def split: option.splits)
  done

crunches reply_unlink_tcb,reply_unlink_sc
for ct_not_queud[wp]: ct_not_queued
and ct_not_in_release_q[wp]: ct_not_in_release_q
  (simp: a_type_def wp: hoare_drop_imp)

lemma test_reschedule_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace> test_reschedule tptr \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: test_reschedule_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; wpsimp)
  done

crunches reply_remove
for scheduler_act_sane[wp]:  "scheduler_act_sane"
  (wp: get_object_wp hoare_drop_imp ignore: test_reschedule)

crunch cur_thread[wp]: tcb_release_enqueue "\<lambda>s. P (cur_thread s)"
  (wp: get_tcb_obj_ref_wp crunch_wps)

crunches set_tcb_obj_ref,set_sc_obj_ref,test_reschedule
for release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
and in_release_queue[wp]: "in_release_queue t::det_state \<Rightarrow> _"
  (wp: get_tcb_obj_ref_wp crunch_wps simp: crunch_simps in_release_queue_def)

lemma tcb_release_remove_in_release_q_neq:
  "\<lbrace>in_release_queue t and K (t \<noteq> tptr)\<rbrace> tcb_release_remove tptr \<lbrace>\<lambda>_. in_release_queue t\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def in_release_queue_def tcb_sched_dequeue_def)

lemma sched_context_donate_in_release_queue_neq:
  "\<lbrace>in_release_queue t and sc_tcb_sc_at (\<lambda>p. p \<noteq> Some t) sc_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. in_release_queue t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp simp: bind_assoc)
   apply wpsimp
  apply (wpsimp simp: set_object_def update_sched_context_def
                wp: get_object_wp tcb_release_remove_in_release_q_neq)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)


lemma sched_context_donate_valid_sched_helper:
  "\<lbrace>valid_sched and bound_sc_tcb_at ((=) None) tptr and not_in_release_q tptr
    and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not>runnable ts) tptr s)\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_not_in_release_q hoare_vcg_imp_lift hoare_vcg_disj_lift
                    set_sc_refills_is_refill_sufficient_indep set_sc_refills_is_refill_ready_indep)
  apply (clarsimp simp: is_tcb_def valid_sched_def active_sc_tcb_at_defs
                        valid_sched_action_def weak_valid_sched_action_def)
  apply (drule_tac x=tptr in spec, clarsimp)
  by (fastforce simp: not_in_release_q_def valid_release_q_def not_queued_def valid_ready_qs_def
                      active_sc_tcb_at_def pred_tcb_at_def obj_at_def)

lemma valid_sched_blocked_imp:
   "\<lbrakk>valid_sched s; not_queued t s; not_in_release_q t s; scheduler_act_not t s; t \<noteq> cur_thread s\<rbrakk> \<Longrightarrow>
             \<not> (st_tcb_at runnable t s \<and> active_sc_tcb_at t s)"
  apply (clarsimp simp: valid_sched_def valid_blocked_def scheduler_act_not_def)
  apply (drule_tac x=t in spec, clarsimp simp:)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
  by (case_tac "tcb_state tcb"; clarsimp)

lemma valid_sched_imp_except_blocked: "valid_sched s \<Longrightarrow> valid_sched_except_blocked s"
  by (clarsimp simp: valid_sched_def)

lemma reschedule_cnt[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_ s. scheduler_action s = choose_new_thread\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  by (wpsimp simp: set_scheduler_action_def wp: thread_get_wp is_schedulable_wp)
     (clarsimp simp: obj_at_def is_schedulable_opt_def is_tcb dest!: get_tcb_SomeD split: option.splits)

lemma set_scheduler_action_cnt_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma test_reschedule_case:
  "\<lbrace>(\<lambda>s. cur_thread s \<noteq> t) and scheduler_act_not t and Q\<rbrace>
      test_reschedule t \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (clarsimp simp: test_reschedule_def scheduler_act_not_def when_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: pred_conj_def; intro conjI impI; wpsimp?)
     apply (rule hoare_assume_pre; clarsimp)+
  done

lemma test_reschedule_case_act:
  "\<lbrace>(\<lambda>s. scheduler_action s = switch_thread t)\<rbrace>
      test_reschedule t \<lbrace>\<lambda>_ s. scheduler_action s = choose_new_thread\<rbrace>"
  apply (wpsimp wp: reschedule_cnt simp: test_reschedule_def)
  done


lemma set_tcb_sched_context_wk_valid_sched_action_except_None:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None
       \<lbrace>\<lambda>_. weak_valid_sched_action_except t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  by (fastforce simp: weak_valid_sched_action_def weak_valid_sched_action_except_2_def
                      active_sc_tcb_at_defs st_tcb_at_kh_if_split refill_prop_defs
                dest!: get_tcb_SomeD split: option.splits)

lemma test_reschedule_valid_sched_action_except_wk_sched_action:
"\<lbrace>valid_sched_action_except_wk_sched_action and weak_valid_sched_action_except t and
   (\<lambda>s. \<not> (st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> \<not> in_release_queue t s))\<rbrace>
      test_reschedule t \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (clarsimp simp: test_reschedule_def scheduler_act_not_def when_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: split del: if_split; wpsimp;
         clarsimp simp: valid_sched_action_def)
  by (clarsimp simp: weak_valid_sched_action_def weak_valid_sched_action_except_2_def)

lemma test_reschedule_valid_sched_except_wk_sched_action:
  notes test_reschedule_valid_sched_action[wp del] if_split[split del]
  shows
  "\<lbrace>valid_sched_except_blocked_except_wk_sched_action and valid_blocked
     and weak_valid_sched_action_except t and bound_sc_tcb_at ((=) None) t\<rbrace>
      test_reschedule t \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: test_reschedule_def scheduler_act_not_def when_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp)
    defer 2
    apply ((wpsimp simp: valid_sched_def valid_sched_action_def wp: reschedule_valid_sched_const)+)[2]
  apply (case_tac "t=x2"; clarsimp)
   defer
   apply (wpsimp simp: weak_valid_sched_action_def weak_valid_sched_action_except_2_def valid_sched_def
      valid_sched_action_def wp: reschedule_valid_sched_const)
  apply (rule_tac Q="\<lambda>_ s. valid_sched s \<and> scheduler_action s = choose_new_thread" in hoare_strengthen_post)
   apply (clarsimp simp: valid_sched_def)
   apply (wpsimp wp: reschedule_required_valid_blocked reschedule_cnt)
  apply clarsimp
  done

lemma set_tcb_sc_update_active_sc_tcb_at_None:
  "\<lbrace>\<lambda>s. True \<rbrace>
      set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>rv s. \<not> (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  by (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def split: if_splits)

lemma sched_context_donate_valid_sched_action:
  (* there is no need for scheduler_act_not on the tcb that owns sc_ptr, because
   test_reschedule will establish that property. valid_sched_action is broken till that point *)
  "\<lbrace>valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp simp: bind_assoc)
   apply (wpsimp wp: set_tcb_sched_context_valid_sched_action_act_not)
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_action_act_not
      test_reschedule_valid_sched_action_except_wk_sched_action)
      apply (wpsimp wp: test_reschedule_sched_act_not)
     apply (wp set_tcb_sched_context_wk_valid_sched_action_except_None hoare_vcg_conj_lift)
      apply (rule_tac Q="\<lambda>_ s. \<not> active_sc_tcb_at a s" in hoare_strengthen_post)
       apply (wpsimp wp: set_tcb_sc_update_active_sc_tcb_at_None)
      apply clarsimp
     apply clarsimp
     apply (wpsimp wp: test_reschedule_sched_act_not)+
  apply (clarsimp simp: valid_sched_action_def)
  done

lemma ssc_in_release_queue[wp]:
  "\<lbrace>\<lambda>s. Q (in_release_queue t s)\<rbrace> set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>\<lambda>_ s. Q (in_release_queue t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=Q] dest!: get_tcb_SomeD)
  apply (auto simp: in_release_queue_def)
  done

lemma sched_context_donate_valid_sched_send_signal_WaitingNtfn_helper:
  notes test_reschedule_valid_sched[wp del]
  shows
    "\<lbrace>valid_sched\<rbrace>
   do _ <- tcb_sched_action tcb_sched_dequeue from_tptr;
      _ <- tcb_release_remove from_tptr;
      _ <- set_tcb_obj_ref tcb_sched_context_update from_tptr None;
      test_reschedule from_tptr
   od
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule_tac Q="\<lambda>s. (valid_sched and scheduler_act_not from_tptr) s \<or>
                         ((valid_sched and (\<lambda>s. scheduler_action s = switch_thread from_tptr)) s)"
         in hoare_weaken_pre)
   apply (rule_tac Q="\<lambda>_ s. valid_sched s \<or> valid_sched s" in hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift)
     apply (wpsimp wp: test_reschedule_valid_sched)
        apply (rule_tac Q="valid_sched_except_blocked and valid_blocked_except from_tptr
                           and not_queued from_tptr and not_in_release_q from_tptr
                           and scheduler_act_not from_tptr"
               in hoare_weaken_pre)
         apply (wpsimp simp: valid_sched_def
                         wp: set_tcb_sched_context_valid_ready_qs_not_queued
                             set_tcb_sched_context_valid_release_q_not_queued
                             set_tcb_sched_context_valid_sched_action_act_not
                             set_tcb_sched_context_valid_blocked_except_None)
        apply simp
       apply (wpsimp wp: tcb_release_remove_valid_blocked_except2 tcb_release_remove_not_in_release_q)
      apply (wpsimp wp: tcb_sched_dequeue_valid_blocked_except_set tcb_dequeue_not_queued
                        tcb_sched_dequeue_valid_ready_qs)
     apply (clarsimp simp: valid_sched_def)
    (* switch_thread from_tptr *)
    apply (wpsimp wp: test_reschedule_valid_sched_except_wk_sched_action)
       apply (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                         set_tcb_sched_context_valid_release_q_not_queued ssc_bound_tcb_at'
                         set_tcb_sched_context_valid_blocked_except_None ssc_st_tcb_at
                         set_tcb_sched_context_wk_valid_sched_action_except_None
                         hoare_vcg_imp_lift set_tcb_sc_update_active_sc_tcb_at_eq)
      apply (wpsimp wp: tcb_release_remove_valid_blocked_except2 tcb_release_remove_not_in_release_q)
     apply (wpsimp wp: tcb_dequeue_not_queued
                       tcb_sched_dequeue_valid_blocked_except_set
                       hoare_vcg_imp_lift tcb_sched_dequeue_valid_ready_qs)
    apply (clarsimp simp: not_in_release_q_def in_release_queue_def)
    apply (clarsimp simp: valid_sched_def valid_sched_action_def valid_blocked_def
                          weak_valid_sched_action_def valid_blocked_except_set_def)
   apply (clarsimp simp: scheduler_act_not_def)+
  done

lemma sched_context_donate_valid_sched:
  "\<lbrace>valid_sched and bound_sc_tcb_at ((=) None) tcb_ptr and st_tcb_at (\<lambda>x. \<not> runnable x) tcb_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def assert_opt_def)
  apply (rule_tac Q="valid_sched and bound_sc_tcb_at ((=) None) tcb_ptr
                and st_tcb_at (\<lambda>x. \<not> runnable x) tcb_ptr and not_in_release_q tcb_ptr" in hoare_weaken_pre)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp simp: )
   apply (wpsimp wp: sched_context_donate_valid_sched_helper)
  apply (rule hoare_seq_ext)
   apply (wpsimp wp: sched_context_donate_valid_sched_helper)
  apply (clarsimp simp: pred_conj_def)
  apply (rule hoare_vcg_conj_lift)
   apply (wpsimp wp: sched_context_donate_valid_sched_send_signal_WaitingNtfn_helper)
  apply (wpsimp wp: ssc_bound_tcb_at_cases hoare_drop_imp tcb_dequeue_not_queued_gen
                    tcb_release_remove_not_in_release_q')
  by (fastforce simp: valid_sched_def valid_release_q_def active_sc_tcb_at_defs
                         not_in_release_q_def)

lemma sched_context_donate_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: test_reschedule_sched_act_not)

lemma reply_unlink_sc_sc_tcb_inactive:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>
   reply_unlink_sc scp rp
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sched_context_def set_object_def
                      get_object_def update_sk_obj_ref_def set_simple_ko_def get_simple_ko_def
                      get_sched_context_def)
  apply (auto simp: partial_inv_def pred_tcb_at_def sc_tcb_sc_at_def obj_at_def)
  done

lemma sts_sc_tcb_sc_at_inactive:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp s \<and> inactive ts \<rbrace>
   set_thread_state t ts \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp s\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
  apply (wp dxo_wp_weak | simp add: set_object_def sc_tcb_sc_at_def)+
  by (clarsimp simp: obj_at_def is_tcb get_tcb_def pred_tcb_at_def)

lemma sc_at_pred_n_state_prop_rewrite:
  "sc_at_pred_n N proj (\<lambda>x. \<forall>y. P x y \<longrightarrow> Q y s) sc s
    \<longleftrightarrow> sc_at_pred_n N (\<lambda>sc. sc) \<top> sc s \<and> (\<forall>y. sc_at_pred_n N proj (\<lambda>x. P x y) sc s \<longrightarrow> Q y s)"
  by (auto simp: sc_at_pred_n_def obj_at_def)

lemma reply_unlink_sc_tcb_tcb_inactive:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>
   reply_unlink_tcb tp rp
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>"
  apply (clarsimp simp: sc_at_pred_n_state_prop_rewrite[where P="\<lambda>to t. to = Some t"]
                        reply_unlink_tcb_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  by (erule disjE
      ; wpsimp wp: sts_sc_tcb_sc_at_inactive hoare_vcg_all_lift hoare_vcg_imp_lift'
                   sts_st_tcb_at_cases)

crunches reply_unlink_tcb
for simple_sched_action[wp]: simple_sched_action
  (wp: hoare_drop_imps)

lemma set_simple_ko_test_sc_refill_max[wp]:
  "set_simple_ko f p new \<lbrace>\<lambda>s. P (test_sc_refill_max t s)\<rbrace>"
  apply (clarsimp simp: set_simple_ko_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp split: option.splits)
  by (intro conjI impI; clarsimp elim!: rsubst[where P=P] split: if_splits kernel_object.splits
                                    simp: a_type_def partial_inv_def obj_at_def test_sc_refill_max_def)

crunches set_thread_state_act, update_sk_obj_ref, get_sk_obj_ref
for test_sc_refill_max[wp]: "\<lambda>s::det_state. P (test_sc_refill_max t s)"
  (simp: set_scheduler_action_def)

lemma set_thread_state_test_sc_refill_max[wp]:
  "set_thread_state st tp \<lbrace>\<lambda>s::det_state. P (test_sc_refill_max t s)\<rbrace>"
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp simp: test_sc_refill_max_def dest!: get_tcb_SomeD)

lemma set_sc_replies_update_test_sc_refill_max[wp]:
  "set_sc_obj_ref sc_replies_update scp replies \<lbrace>\<lambda>s. P (test_sc_refill_max t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (auto simp: obj_at_def test_sc_refill_max_def)

lemma update_sc_replies_update_test_sc_refill_max[wp]:
  "update_sched_context scp (sc_replies_update f) \<lbrace>\<lambda>s. P (test_sc_refill_max t s)\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (auto simp: obj_at_def test_sc_refill_max_def)

lemma reply_unlink_sc_test_sc_refill_max[wp]:
  "reply_unlink_sc sp rp \<lbrace>\<lambda>s::det_state. P (test_sc_refill_max t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_sc_def)

lemma reply_unlink_tcb_test_sc_refill_max[wp]:
  "reply_unlink_tcb tp rp \<lbrace>\<lambda>s::det_state. P (test_sc_refill_max t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_tcb_def)

crunches update_sk_obj_ref, get_sk_obj_ref
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"

lemma reply_unlink_sc_active_sc_tcb_at[wp]:
 "\<lbrace>active_sc_tcb_at t\<rbrace>
     reply_unlink_sc scp rptr \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  by (wpsimp wp: hoare_vcg_imp_lift get_simple_ko_wp active_sc_tcb_at_update_sched_context_no_change)

lemma set_sc_obj_ref_no_tcb_update[wp]:
  "set_sc_obj_ref f scp new \<lbrace>ko_at (TCB tcb) t\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  by (wpsimp simp: set_object_def wp: get_object_wp simp: obj_at_def)

lemma set_reply_obj_ref_no_tcb_update[wp]:
  "set_reply_obj_ref f rp new \<lbrace>ko_at (TCB tcb) t\<rbrace>"
  apply (clarsimp simp: update_sk_obj_ref_def set_simple_ko_def)
  by (wpsimp simp: set_object_def wp: get_simple_ko_wp get_object_wp simp: obj_at_def)

lemma set_reply_no_tcb_update[wp]:
  "set_reply ptr new \<lbrace>ko_at (TCB tcb) t\<rbrace>"
  apply (clarsimp simp: set_simple_ko_def)
  by (wpsimp simp: set_object_def wp: get_object_wp simp: obj_at_def)

lemma reply_unlink_sc_no_tcb_update[wp]:
  "reply_unlink_sc sp rp \<lbrace>ko_at (TCB tcb) t\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  by (wpsimp wp: hoare_vcg_imp_lift get_simple_ko_wp)

lemma sts_tcb_ko_at':
  "\<lbrace>\<lambda>s. \<forall>v'. v = (if t = t' then v' \<lparr>tcb_state := ts\<rparr> else v')
              \<and> ko_at (TCB v') t' s \<and> P v\<rbrace>
      set_thread_state t ts
   \<lbrace>\<lambda>rv s. ko_at (TCB v) t' s \<and> P v\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

text \<open>The reply a TCB is waiting on\<close>
definition
  reply_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "reply_blocked ts \<equiv> case ts of
     BlockedOnReceive ep (Some r) \<Rightarrow> Some r
   | BlockedOnReply r \<Rightarrow> Some r
   | _ \<Rightarrow> None"

lemma reply_remove_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))
    and (\<lambda>s. reply_sc_reply_at (\<lambda>p. \<forall>scp. p = Some scp
             \<longrightarrow> sc_tcb_sc_at (\<lambda>x. x \<noteq> Some t) scp s) rptr s) \<comment> \<open>callee\<close>\<rbrace>
     reply_remove tptr rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply (wpsimp wp: sched_context_donate_active_sc_tcb_at_neq gbn_wp
                    static_imp_wp hoare_vcg_if_lift2)
  apply (rename_tac sc_ptr sc n)
  apply (drule(1) valid_objs_ko_at)
  subgoal for reply s sc_ptr sc n
    apply (auto simp: valid_obj_def valid_reply_def reply_tcb_reply_at_def
                      active_sc_tcb_at_defs reply_sc_reply_at_def
                      sc_tcb_sc_at_def is_tcb is_reply sc_at_pred_def
               dest!: sc_with_reply_SomeD
                      sym_refs_reply_sc_reply_at[where reply_ptr=rptr and sc_ptr=sc_ptr
                                                   and list="tl (sc_replies sc)"]
              intro!: hd_Cons_tl)
    done .

lemma set_tcb_sc_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> set_tcb_obj_ref tcb_sched_context_update tp scnew
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def dest!: get_tcb_SomeD)

lemma update_sched_context_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> update_sched_context sp f
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

crunches tcb_sched_action (* why do we need this? *)
for reply_tcb_reply_at'[wp]: "reply_tcb_reply_at P s"

lemma reschedule_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> reschedule_required
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
    apply ((wpsimp simp: set_scheduler_action_def)+)[2]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rename_tac schedulable)
  apply (case_tac schedulable; clarsimp simp: bind_assoc assert_opt_def)
   defer
   apply (wpsimp simp: set_scheduler_action_def, clarsimp simp: reply_tcb_reply_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rename_tac scp_opt)
  apply (case_tac scp_opt; simp)
  apply (rename_tac scp)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp simp: set_scheduler_action_def)
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

lemma test_reschedule_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> test_reschedule tptr
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  by (wpsimp simp: test_reschedule_def set_object_def
                wp: reschedule_reply_tcb_reply_at_act_not get_object_wp)

lemma tcb_release_remove_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> tcb_release_remove tptr
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def
                wp: reschedule_reply_tcb_reply_at_act_not get_object_wp)

lemma sched_context_donate_reply_tcb_reply_at_act_not:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace> sched_context_donate scp tp
      \<lbrace>\<lambda>rv s. reply_tcb_reply_at
                (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s)
                rp s\<rbrace>"
  by (wpsimp simp: sched_context_donate_def set_sc_obj_ref_def get_sc_obj_ref_def tcb_sched_action_def
               wp: set_tcb_sc_reply_tcb_reply_at_act_not update_sched_context_reply_tcb_reply_at_act_not
                   test_reschedule_reply_tcb_reply_at_act_not tcb_release_remove_reply_tcb_reply_at_act_not
                 get_object_wp hoare_vcg_all_lift hoare_drop_imps hoare_vcg_if_lift2)

lemma valid_sched_not_runnable_not_inq:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s \<and> not_in_release_q tptr s"
  by (fastforce simp: valid_sched_def valid_ready_qs_def valid_release_q_def pred_tcb_at_def
                      not_queued_def not_in_release_q_def obj_at_def)

lemma valid_sched_no_active_sc_not_inq:
  "\<lbrakk>valid_sched s; \<not> active_sc_tcb_at tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s \<and> not_in_release_q tptr s"
  by (fastforce simp: valid_sched_def valid_ready_qs_def valid_release_q_def pred_tcb_at_def
                      not_queued_def not_in_release_q_def obj_at_def)

lemma valid_sched_not_runnable_scheduler_act_not:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def pred_tcb_at_def
                       scheduler_act_not_def obj_at_def)

lemma valid_sched_no_active_sc_scheduler_act_not:
  "\<lbrakk>valid_sched s; \<not> active_sc_tcb_at tptr s\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def pred_tcb_at_def
                       scheduler_act_not_def obj_at_def)

lemma valid_sched_in_release_q_scheduler_act_not:
  "\<lbrakk>valid_sched s; in_release_queue tptr s\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def pred_tcb_at_def
                       scheduler_act_not_def obj_at_def in_release_queue_def)

lemma valid_sched_not_schedulable_sc_not_queued:
  "\<lbrakk>valid_sched s; \<not> is_schedulable_bool tptr (in_release_queue tptr s) s; tcb_at tptr s\<rbrakk>
     \<Longrightarrow> in_release_queue tptr s \<or> not_queued tptr s"
  by (fastforce simp: valid_sched_def valid_ready_qs_def valid_release_q_def is_tcb etcb_defs
                     not_queued_def not_in_release_q_def active_sc_tcb_at_defs
                     is_schedulable_bool_def get_tcb_rev
          split: option.splits)

lemma reply_remove_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s
        \<and> reply_tcb_reply_at (\<lambda>t. \<exists>tp. t = Some tp \<and> scheduler_act_not tp s
                                       \<and> st_tcb_at (\<lambda>ts. \<not>runnable ts) tp s) rp s\<rbrace>
     reply_remove tp rp
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp simp: assert_opt_def)
  apply (wpsimp simp: obj_at_def reply_tcb_reply_at_def
                  wp: sched_context_donate_valid_sched reply_unlink_tcb_valid_sched
                      gbn_wp static_imp_wp hoare_vcg_if_lift2)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma reply_remove_tcb_valid_sched:
  "\<lbrace>valid_sched\<rbrace>
     reply_remove_tcb tp rp
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply (wpsimp wp: reply_remove_valid_sched reply_unlink_tcb_valid_sched get_sk_obj_ref_wp)
  done

lemma has_budget_def2:
  "has_budget t s = has_budget_kh t (cur_time s) (kheap s)"
  by (clarsimp simp: has_budget_def)

lemma valid_ntfn_q_def2:
  "(valid_ntfn_q :: det_state \<Rightarrow> _) s =
   ((\<forall>tp np. ntfn_at_pred (\<lambda>ntfn. tp \<in> set (ntfn_queue (ntfn))) np s \<longrightarrow>
    tp \<noteq> cur_thread s \<and>
    tp \<noteq> idle_thread s \<and>
    has_budget tp s \<and>
    st_tcb_at (\<lambda>ts. ts = BlockedOnNotification np) tp s))"
  unfolding valid_ntfn_q_def
  apply (rule iffI; clarsimp)
   apply (drule_tac x=np in spec; clarsimp simp: simple_obj_at_def has_budget_def2)
  apply (clarsimp split: option.splits)
  apply (case_tac x2; clarsimp)
   apply (drule_tac x=t and y = p in spec2)
   apply (clarsimp simp: has_budget_def2 simple_obj_at_def)
  done

lemma set_ntfn_obj_ref_valid_ntfn_q:
  "\<forall>ntfn. ntfn_queue ((f (\<lambda>y. ep) ntfn)) = ntfn_queue ((ntfn)) \<Longrightarrow>
  \<lbrace>valid_ntfn_q\<rbrace> set_ntfn_obj_ref f ptr ep \<lbrace>\<lambda>rv. valid_ntfn_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (subst valid_ntfn_q_def2)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (wpsimp simp: has_budget_def2 wp: hoare_vcg_disj_lift)
  apply (clarsimp simp: simple_obj_at_def valid_ntfn_q_def2 obj_at_def)
   apply (case_tac "xa = ptr"; simp)
   apply (drule_tac x=x and y = xa in spec2; clarsimp simp: has_budget_def2)
   apply (drule_tac x=x and y = xa in spec2; clarsimp simp: has_budget_def2)
  done

lemma set_ntfn_sc_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_ntfn_obj_ref ntfn_sc_update ptr ep \<lbrace>\<lambda>rv. valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_ntfn_obj_ref_valid_ntfn_q simp: ntfn_queue_def)

lemma set_ntfn_bound_tcb_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_ntfn_obj_ref ntfn_bound_tcb_update ptr ep \<lbrace>\<lambda>rv. valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_ntfn_obj_ref_valid_ntfn_q simp: ntfn_queue_def)

lemma unbind_maybe_notification_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> unbind_maybe_notification ptr \<lbrace>\<lambda>_. valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: unbind_maybe_notification_def)
  apply (wpsimp wp: hoare_drop_imp set_bound_notification_valid_ntfn_q)
  done

lemma unbind_maybe_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_maybe_notification ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: unbind_maybe_notification_def)
  apply (wpsimp wp: hoare_drop_imp set_bound_notification_valid_sched)
  done

lemma sched_context_update_consumed_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def split: if_splits)
  apply (rule conjI; clarsimp)
  apply (rule_tac x=scpa in exI, clarsimp)+
  done

lemma sched_context_update_consumed_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def split: if_splits)
  apply (rule conjI; clarsimp)
   apply (rule_tac x=scpa in exI, fastforce)+
  done

lemma sched_context_update_consumed_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def split: if_splits)
  apply (rule conjI; clarsimp)
   apply (rule_tac x=scpa in exI, fastforce)+
  done

(* FIXME maybe move *)
lemma sched_context_update_consumed_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   sched_context_update_consumed scp
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def update_sched_context_def set_object_def
                  wp: get_object_wp
                split_del: if_split)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

(* FIXME maybe move *)
lemma set_consumed_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   set_consumed scp buf
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  by (wpsimp simp: set_consumed_def)

(* FIXME maybe move *)
crunches set_consumed, sched_context_update_consumed
  for tcb_ready_time[wp]: "\<lambda>s. P (tcb_ready_time t s) (tcb_ready_time t' s)"
    (rule: release_queue_cmp_lift)

crunches set_consumed
for active_sc_tcb_at[wp]: "\<lambda>s. P (active_sc_tcb_at t (s::det_state))"
and budget_sufficient[wp]: "\<lambda>s::det_state. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s::det_state. P (budget_ready t s)"

lemma set_consumed_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_consumed scp buf \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift split_del: if_split)

(* FIXME maybe move *)
lemma sc_yf_update_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_sc_obj_ref sc_yield_from_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

(* FIXME maybe move *)
lemma sc_yf_update_tcb_ready_time[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s) (tcb_ready_time t' s)\<rbrace>
       set_sc_obj_ref sc_yield_from_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s) (tcb_ready_time t' s)\<rbrace>"
  by (rule hoare_lift_Pf3[where f="\<lambda>s. tcb_ready_time t' s"]; wpsimp)

(* FIXME maybe move *)
lemma tcb_yt_update_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update tptr new
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

(* FIXME maybe move *)
lemma tcb_yt_update_tcb_ready_time[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s) (tcb_ready_time t' s)\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update tptr new
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s) (tcb_ready_time t' s)\<rbrace>"
  by (rule hoare_lift_Pf3[where f="\<lambda>s. tcb_ready_time t' s"]; wpsimp)

(* FIXME maybe move *)
lemma complete_yield_to_tcb_ready_time'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
   complete_yield_to tp
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  by (wpsimp simp: complete_yield_to_def wp: hoare_drop_imps)

(* FIXME maybe move *)
crunches complete_yield_to
  for tcb_ready_time[wp]: "\<lambda>s. P (tcb_ready_time t s) (tcb_ready_time t' s)"
    (rule: release_queue_cmp_lift)

lemma complete_yield_to_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> complete_yield_to tp \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def get_sk_obj_ref_def)
              apply (wpsimp simp: set_tcb_obj_ref_def wp: hoare_drop_imp)+
  by (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def set_tcb_obj_ref_def)+

lemma cancel_signal_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     cancel_signal tptr ntfnptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched hoare_drop_imps)
  apply (clarsimp elim!: valid_sched_not_runnable_scheduler_act_not
                    simp: pred_tcb_at_def obj_at_def)
  done

crunch st_tcb_at_not_runnable[wp]: reply_remove_tcb "st_tcb_at (\<lambda>st. \<not>runnable st) t::det_state \<Rightarrow> _"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps wp_del: reply_remove_st_tcb_at)

lemma blocked_cancel_ipc_valid_sched_Send:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     blocked_cancel_ipc (BlockedOnSend ep data) tptr None
   \<lbrace>\<lambda>rv. valid_sched ::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched simp: get_blocking_object_def)
  apply (clarsimp elim!: valid_sched_not_runnable_scheduler_act_not
                    simp: pred_tcb_at_def obj_at_def)
  done

lemma blocked_cancel_ipc_valid_sched_Receive:
  "\<lbrace>valid_sched
    and (\<lambda>s. st_tcb_at ((=) (BlockedOnReceive ep reply_opt)) tptr s)\<rbrace>
     blocked_cancel_ipc (BlockedOnReceive ep reply_opt) tptr reply_opt
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply etcbs_of'_non_tcb_update[simp]
  apply (simp add: blocked_cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gbi_ep_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ get_epq_sp])
  apply (cases reply_opt; clarsimp)
   apply (wpsimp wp: set_thread_state_not_runnable_valid_sched get_simple_ko_wp
      reply_unlink_tcb_valid_sched get_object_wp
      simp: set_simple_ko_def set_object_def pred_tcb_at_eq_commute)
  apply (intro conjI; clarsimp elim!: valid_sched_not_runnable_scheduler_act_not
                    simp: pred_tcb_at_def obj_at_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched get_simple_ko_wp
      reply_unlink_tcb_valid_sched get_object_wp
      simp: set_simple_ko_def set_object_def)
  apply (clarsimp cong: conj_cong simp: partial_inv_def pred_tcb_at_eq_commute)
  apply (rule conjI)
   defer
  apply (intro conjI; clarsimp elim!: valid_sched_not_runnable_scheduler_act_not
                    simp: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: valid_sched_def obj_at_def pred_tcb_at_def split: if_split_asm)
  apply (intro conjI)
     apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
     apply (intro conjI impI, fastforce)
       apply (clarsimp simp: active_sc_tcb_at_defs)
       apply (drule_tac x=d and y=p in spec2, clarsimp)
       apply (drule_tac x=t in bspec, simp, clarsimp)
       apply (rename_tac scp)
       apply (rule_tac x=scp in exI, clarsimp)
      apply (clarsimp simp: active_sc_tcb_at_defs refill_sufficient_kh_def is_refill_sufficient_def)
      apply (drule_tac x=d and y=p in spec2, clarsimp)
      apply (drule_tac x=t in bspec, simp, clarsimp)
      apply (rename_tac scp sc n)
      apply (rule_tac x=scp in exI, clarsimp)
     apply (clarsimp simp: active_sc_tcb_at_defs refill_ready_kh_def is_refill_ready_def)
     apply (drule_tac x=d and y=p in spec2, clarsimp)
     apply (drule_tac x=t in bspec, simp, clarsimp)
     apply (rename_tac scp sc n)
     apply (rule_tac x=scp in exI, clarsimp)
    apply solve_valid_release_q
   apply (clarsimp simp: valid_sched_action_def, rule conjI)
    apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs refill_prop_defs
                  split: option.splits)
   apply (intro impI conjI; fastforce?)
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=t in spec)
  apply (clarsimp simp: st_tcb_at_kh_def active_sc_tcb_at_defs split: if_splits)
  done

context DetSchedSchedule_AI begin

crunches sched_context_unbind_yield_from
for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
  (wp: maybeM_inv mapM_x_wp')

crunches update_sk_obj_ref
for cur_time[wp]: "\<lambda>s::det_state. P (cur_time s)"
  (wp: maybeM_inv mapM_x_wp' hoare_drop_imp)

lemma sched_context_unbind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_unbind_ntfn scptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_ntfn_def maybeM_def)
  by (wpsimp wp: update_sched_context_valid_sched hoare_drop_imp hoare_vcg_all_lift
      simp:  get_sc_obj_ref_def)

lemma sched_context_maybe_unbind_ntfn_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> sched_context_maybe_unbind_ntfn scptr \<lbrace>\<lambda>rv. valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_maybe_unbind_ntfn_def)
  by (wpsimp simp: get_sk_obj_ref_def
               wp: hoare_drop_imps)

lemma sched_context_maybe_unbind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_maybe_unbind_ntfn scptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_maybe_unbind_ntfn_def)
  by (wpsimp simp: set_sc_obj_ref_def update_sk_obj_ref_def get_sk_obj_ref_def
               wp: hoare_drop_imps update_sched_context_valid_sched)

(* FIXME: Move *)
lemma sym_ref_tcb_reply_Receive:
   "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_state tcb = BlockedOnReceive ep (Some rp) \<rbrakk> \<Longrightarrow>
  \<exists>reply. kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some tp"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def get_refs_def2 elim!: sym_refsE)
  apply (drule_tac x="(rp, TCBReply)" in bspec)
   apply fastforce
  apply (clarsimp simp: obj_at_def)
  apply (case_tac koa; clarsimp simp: get_refs_def2)
  done

lemma cancel_ipc_valid_sched:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s)) and valid_sched\<rbrace>
      cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (wpsimp wp: hoare_vcg_all_lift reply_remove_tcb_valid_sched
                    blocked_cancel_ipc_valid_sched_Receive
                    blocked_cancel_ipc_valid_sched_Send
                    thread_set_not_state_valid_sched thread_set_no_change_tcb_pred
                    hoare_vcg_imp_lift gts_wp)
  by (fastforce elim!: st_tcb_weakenE)+

end

(* valid_ready_qs with thread not runnable *)
lemma tcb_sched_dequeue_strong_valid_sched:
  "\<lbrace>ct_not_in_q and valid_sched_action and ct_in_cur_domain and
    valid_blocked and st_tcb_at (\<lambda>st. \<not> runnable st) thread and
    (\<lambda>es. \<forall>d p. (\<forall>t\<in>set (ready_queues es d p). is_etcb_at' t (etcbs_of es) \<and>
        etcb_at (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) t es \<and>
        (t \<noteq> thread \<longrightarrow> st_tcb_at runnable t es \<and> active_sc_tcb_at t es
                        \<and> budget_ready t es \<and> budget_sufficient t es))
          \<and> distinct (ready_queues es d p)) and valid_release_q and
    valid_idle_etcb\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def valid_sched_def split: option.split dest!: get_tcb_SomeD)
  apply (intro conjI impI allI)
   apply (fastforce simp: etcb_at_def etcbs_of'_def is_etcb_at_def valid_ready_qs_def2
                          tcb_sched_dequeue_def obj_at_def)
   apply (fastforce simp: ct_not_in_q_def not_queued_def tcb_sched_dequeue_def)
  apply (clarsimp simp: valid_blocked_def tcb_sched_dequeue_def)
  apply (case_tac "t=thread")
   apply simp
   apply (force simp: st_tcb_at_def obj_at_def)
  apply (erule_tac x=t in allE)
  apply (erule impE)
   apply (clarsimp simp: not_queued_def split: if_split_asm)
   apply (erule_tac x=d in allE)
   apply force
  apply force
  done

(* This is not nearly as strong as it could be *)
lemma possible_switch_to_simple_sched_action:
  "\<lbrace>simple_sched_action and (\<lambda>s. \<not> in_cur_domain target s)\<rbrace>
       possible_switch_to target \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  apply (wpsimp wp: get_tcb_obj_ref_wp)
  apply (clarsimp simp: obj_at_def in_cur_domain_def etcb_at_def etcbs_of'_def)
  done

lemma possible_switch_to_valid_blocked_const:
  "\<lbrace>valid_blocked_except_set S \<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_blocked_except_set S ::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const reschedule_required_valid_blocked thread_get_wp
      simp: set_scheduler_action_def get_tcb_obj_ref_def)
  apply (clarsimp simp: obj_at_def valid_blocked_def pred_tcb_at_def is_tcb)
  done

lemma possible_switch_to_ct_in_cur_domain[wp]:
  "possible_switch_to target \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding possible_switch_to_def set_scheduler_action_def
  by (wpsimp wp: get_tcb_obj_ref_wp)

crunches tcb_sched_action
for not_cur_thread[wp]: "not_cur_thread t"

lemma possible_switch_to_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> possible_switch_to tptr \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: thread_get_wp)
  by (clarsimp simp: obj_at_def is_tcb)

crunches set_scheduler_action, possible_switch_to
for budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and not_in_release_q[wp]: "not_in_release_q t"
  (wp: crunch_wps)

crunch simple[wp]: update_sk_obj_ref,reply_unlink_sc,reply_unlink_tcb,reply_remove simple_sched_action
  (simp: a_type_def wp: hoare_drop_imps)

lemma sched_context_unbind_tcb_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)

crunches set_thread_state
  for cur_domain'[wp]: "\<lambda>s. P (cur_domain s)"

lemma set_thread_state_in_cur_domain[wp]:
  "set_thread_state p st \<lbrace>in_cur_domain t::det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=etcbs_of], rule hoare_lift_Pf[where f=cur_domain]; wp)

lemma set_thread_state_in_cur_domain'[wp]:
  "set_thread_state p st \<lbrace>\<lambda>s. P (in_cur_domain t s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=etcbs_of], rule hoare_lift_Pf[where f=cur_domain];wp)

crunch simple[wp]: unbind_from_sc,sched_context_unbind_all_tcbs simple_sched_action
  (wp: maybeM_wp crunch_wps hoare_vcg_all_lift)

crunch scheduler_act_not[wp]: unbind_from_sc "scheduler_act_not t"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

crunches cancel_ipc
for simple_sched_action[wp]: simple_sched_action
and scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: maybeM_wp hoare_drop_imps)

crunches unbind_maybe_notification, unbind_notification,
         sched_context_maybe_unbind_ntfn, reply_unlink_sc,
         sched_context_unbind_ntfn
  for  not_queued'[wp]: "not_queued t"
  and not_in_release_q'[wp]: "\<lambda>s:: det_state. P (not_in_release_q t s)"
  and  scheduler_act_not[wp]: "scheduler_act_not t"
    (wp: crunch_wps maybeM_inv simp: get_sc_obj_ref_def)

crunches blocked_cancel_ipc,cancel_signal
  for not_queued[wp]: "not_queued t"
  and not_in_release_q[wp]: "not_in_release_q t:: det_state \<Rightarrow> _"
  (wp: hoare_drop_imp)

lemma cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t:: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; wpsimp)
  done

lemma valid_sched_release_queue_cong:
  "set queue = set queue' \<Longrightarrow>
     distinct queue \<Longrightarrow> distinct queue' \<Longrightarrow>
     sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) queue \<Longrightarrow>
     sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) queue' \<Longrightarrow>
       valid_sched_2  (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s)
                         (kheap s) (cur_thread s) (idle_thread s) queue
      = valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s)
                         (kheap s) (cur_thread s) (idle_thread s) queue'"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def sorted_release_q_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

lemma distinct_zip_snd_unique:
  "\<lbrakk>distinct xs; (a, b) \<in> set (zip xs ys); (a, b') \<in> set (zip xs ys)\<rbrakk>
     \<Longrightarrow> b = b'"
  apply (induct xs arbitrary: ys, simp)
  apply (clarsimp simp: zip_Cons1)
  apply (erule disjE, fastforce dest!: in_set_zipE)
  apply (erule disjE, fastforce dest!: in_set_zipE, clarsimp)
  done

lemma tcb_release_enqueue_in_release_q:
  "\<lbrace>\<top>\<rbrace> tcb_release_enqueue tcbptr \<lbrace>\<lambda>ya. in_release_q tcbptr\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. in_queue_2 (tcbptr # qs) tcbptr
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: valid_sched_release_queue_cong)
   apply (clarsimp simp: in_queue_2_def
                    pred_tcb_at_def obj_at_def split: option.splits)+
  done

lemma tcb_release_enqueue_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (active_sc_tcb_at t s)\<rbrace>
   tcb_release_enqueue t'
   \<lbrace>\<lambda>_ s :: det_state. Q (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def get_sc_time_def get_tcb_sc_def bind_assoc assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rename_tac tcb_sc)
  apply (case_tac tcb_sc; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (induct_tac qs)
    apply (wpsimp wp: mapM_wp')
   apply (wpsimp simp: mapM_Cons)
  by (auto simp: active_sc_tcb_at_defs  split: option.splits)

lemma valid_release_q_release_queue_cong:
  "set queue = set queue' \<Longrightarrow>
     distinct queue \<Longrightarrow> distinct queue' \<Longrightarrow>
     sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) queue \<Longrightarrow>
     sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) queue' \<Longrightarrow>
        valid_release_q_2 queue (kheap s) = valid_release_q_2 queue' (kheap s)"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def sorted_release_q_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

lemma valid_sched_action_release_queue_cong:
  "set queue = set queue' \<Longrightarrow> distinct queue \<Longrightarrow> distinct queue'
   \<Longrightarrow> valid_sched_action_2 (scheduler_action s) (kheap s) (cur_thread s) (cur_domain s) (cur_time s) queue
       = valid_sched_action_2 (scheduler_action s) (kheap s) (cur_thread s) (cur_domain s) (cur_time s) queue'"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

(* FIXME move *)
lemma valid_release_q_active_sc:
  "valid_release_q s \<Longrightarrow> t \<in> set (release_queue s) \<Longrightarrow> active_sc_tcb_at t s"
  by (clarsimp simp: valid_release_q_def active_sc_tcb_at_def)

lemma tcb_release_enqueue_valid_release_q[wp]:
  "\<lbrace> valid_release_q and active_sc_tcb_at t and st_tcb_at runnable t and not_in_release_q t\<rbrace>
     tcb_release_enqueue t
   \<lbrace>\<lambda>_. valid_release_q \<rbrace>"
  apply (unfold tcb_release_enqueue_def pred_conj_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ mapM_get_sc_time_sp])
  apply wp
  apply (elim conjE)
  apply (simp only: split_def valid_release_q_def)
  apply (simp del: set_map)
  apply (subst filter_zip_split)+
  apply (intro conjI; (fastforce simp: not_in_release_q_def)?)
  apply (simp only: sorted_release_q_def)
  apply (clarsimp simp: sorted_append sorted_map[symmetric] sorted_filter)
  apply (intro conjI impI allI; clarsimp)
  by (drule_tac x=x in bspec, simp;
      fastforce simp: pred_tcb_at_def obj_at_def tcb_ready_time_def get_tcb_def
                split: option.splits dest!: get_tcb_SomeD)+

crunches tcb_release_enqueue
  for valid_ready_qs[wp]: valid_ready_qs
  and ct_not_in_q[wp]: ct_not_in_q
  and ct_in_cur_domain[wp]: ct_in_cur_domain
  and etcb_at[wp]: "etcb_at P t"
    (wp: mapM_wp' crunch_wps simp: crunch_simps)

lemma tcb_release_enqueue_valid_sched_action[wp]:
  "\<lbrace> scheduler_act_not thread
    and valid_sched_action
    and st_tcb_at runnable thread and active_sc_tcb_at thread\<rbrace>
      tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ mapM_get_sc_time_sp])
  apply wpsimp
  apply (clarsimp simp: split_def valid_sched_action_def weak_valid_sched_action_def scheduler_act_not_def
              simp del: set_map)
  by ((subst filter_zip_split)+, fastforce)

(* FIXME maybe move *)
lemma not_in_release_q_set_lift:
 "set A = set B \<Longrightarrow> not_in_release_q_2 A t = not_in_release_q_2 B t"
  by (clarsimp simp: not_in_release_q_2_def in_queue_2_def)

(* FIXME move *)
lemma distinct_shuffle_left:
  "distinct (A @ x # B) = distinct (x # A @ B)"
  by fastforce

lemma tcb_release_enqueue_set_ident:
  "length qs = length r \<Longrightarrow>
   set (map fst (filter (\<lambda>(_, t'). t' \<le> time) (zip qs r))
        @ tcb_ptr
        # map fst (filter (\<lambda>(_, t'). \<not> t' \<le> time) (zip qs r)))
   = set (tcb_ptr # qs)"
  apply (subgoal_tac "set qs = (fst ` {x \<in> set (zip qs r). case x of (uu_, t') \<Rightarrow> t' \<le> time} \<union>
                                fst ` {x \<in> set (zip qs r). case x of (uu_, t') \<Rightarrow> \<not> t' \<le> time}) ")
   apply simp
  apply (clarsimp simp: image_def Collect_disj_eq[symmetric])
  apply (subgoal_tac "\<And>y. ((\<exists>b. (y, b) \<in> set (zip qs r) \<and> b \<le> time) \<or>
              (\<exists>b. (y, b) \<in> set (zip qs r) \<and> \<not> b \<le> time)) = (\<exists>b. (y, b) \<in> set (zip qs r))")
   apply (simp)
   apply (clarsimp simp: set_eq_subset subset_eq)
   apply (intro conjI)
    apply (fastforce elim: length_eq_pair_in_set_zip)
   apply (fastforce dest: in_set_zip1)
  apply fastforce
  done

lemma tcb_release_enqueue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert tcb_ptr S)\<rbrace>
   tcb_release_enqueue tcb_ptr
   \<lbrace>\<lambda>xa. valid_blocked_except_set S\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. valid_blocked_except_set_2 S (ready_queues s)
            (tcb_ptr # qs)
            (kheap s) (scheduler_action s) (cur_thread s)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length)
   prefer 2
   apply (clarsimp simp: valid_blocked_except_set_def pred_tcb_at_def obj_at_def
                  split: option.splits)
   apply (subgoal_tac "not_in_release_q_2 (release_queue s) t \<and> t \<noteq> tcb_ptr")
    apply fastforce
   apply (clarsimp simp: not_in_release_q_def)
  apply (clarsimp simp: valid_blocked_except_set_def pred_tcb_at_def obj_at_def
                 split: option.splits)
  apply (subgoal_tac "not_in_release_q_2 (tcb_ptr # qs) t")
   apply fastforce
  apply (subst not_in_release_q_set_lift[OF tcb_release_enqueue_set_ident, symmetric];
         assumption)
  done

lemma tcb_release_enqueue_valid_sched:
  "\<lbrace> not_queued thread and not_in_release_q thread
    and scheduler_act_not thread
    and valid_sched_except_blocked and valid_blocked_except thread
    and st_tcb_at runnable thread and active_sc_tcb_at thread\<rbrace>
      tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def wp: tcb_release_enqueue_valid_blocked_except_set)

lemma valid_blocked_divided:
  "valid_blocked s
   = (valid_blocked_except_set S s \<and>
      (\<forall>t st. t \<in> S \<longrightarrow> not_queued t s \<longrightarrow> not_in_release_q t s
                    \<longrightarrow> st_tcb_at ((=) st) t s \<longrightarrow> t \<noteq> cur_thread s
                    \<longrightarrow> scheduler_action s \<noteq> switch_thread t
                    \<longrightarrow> (\<not>  active st \<or> \<not> active_sc_tcb_at t s)))"
  by (auto simp: valid_blocked_def valid_blocked_except_set_def)

lemma valid_blocked_divided2:
  "valid_blocked_except_set S s
   \<Longrightarrow> (\<forall>t st. t \<in> S \<longrightarrow> not_queued t s \<longrightarrow> not_in_release_q t s
               \<longrightarrow> st_tcb_at ((=) st) t s \<longrightarrow> t \<noteq> cur_thread s
               \<longrightarrow> scheduler_action s \<noteq> switch_thread t
               \<longrightarrow> (\<not>  active st \<or> \<not> active_sc_tcb_at t s))
   \<Longrightarrow> valid_blocked s"
  by (auto simp: valid_blocked_def valid_blocked_except_set_def)

lemma tcb_release_enqueue_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked
    and not_in_release_q thread
    and scheduler_act_not thread
    and st_tcb_at runnable thread and active_sc_tcb_at thread\<rbrace>
     tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked :: det_state \<Rightarrow> _\<rbrace>"
  by wpsimp

lemma test_possible_switch_to_valid_sched:
  "\<lbrace>\<lambda>s. if (st_tcb_at runnable target s \<and> active_sc_tcb_at target s \<and> not_in_release_q target s)
        then (valid_sched_except_blocked s \<and> valid_blocked_except target s
              \<and> (target \<noteq> idle_thread s) \<and> budget_ready target s \<and> budget_sufficient target s)
        else (valid_sched s) \<rbrace>
     test_possible_switch_to target
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding test_possible_switch_to_def gets_the_def
  apply (wpsimp wp: possible_switch_to_valid_sched_strong is_schedulable_wp)
  apply (intro conjI; intro impI allI)
   apply (intro conjI; intro impI allI;
          clarsimp simp: dest!: is_schedulable_opt_Some)
   apply (subgoal_tac "(st_tcb_at runnable target s \<and> active_sc_tcb_at target s) = False";
          clarsimp simp: not_in_release_q_def in_release_queue_def)
  apply (subgoal_tac "(active_sc_tcb_at target s \<and> not_in_release_q target s) = False";
         clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
  done

lemma postpone_valid_sched: (* sc_ptr is linked to a thread that is not in any queue *)
  "\<lbrace>valid_sched_except_blocked and
    (\<lambda>s. \<forall> tp. sc_tcb_sc_at ((=) (Some tp)) sc_ptr s \<longrightarrow>
      (valid_blocked_except tp s \<and> st_tcb_at runnable tp s \<and> scheduler_act_not tp s
      \<and> not_in_release_q tp s \<and> not_queued tp s \<and> active_sc_tcb_at tp s
     ))\<rbrace>
    postpone sc_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched
            tcb_sched_dequeue_not_queued_inv
            tcb_sched_dequeue_valid_ready_qs)
  done

lemma postpone_valid_sched_invs: (* sc_ptr is linked to a thread that is not in any queue *)
  "\<lbrace>valid_sched_except_blocked and invs and
      sc_with_tcb_prop sc_ptr
           (\<lambda>tp s. st_tcb_at runnable tp s \<and> scheduler_act_not tp s
           \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s
           \<and> valid_blocked_except tp s)\<rbrace>
    postpone sc_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched
                    tcb_dequeue_not_queued
                    tcb_sched_dequeue_valid_ready_qs
                    tcb_sched_dequeue_valid_blocked_except_set_const)
  by (drule (2) sc_with_tcb_prop_rev') wpsimp

(*
lemma postpone_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and
   (\<lambda>s. \<forall> tp. sc_tcb_sc_at (\<lambda>p. p = Some tp) sc_ptr s \<longrightarrow>
      (st_tcb_at runnable tp s
      \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s
      \<and> scheduler_act_not tp s))\<rbrace>
    postpone sc_ptr
   \<lbrace>\<lambda>_. valid_sched_except_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched_except_blocked
            tcb_sched_dequeue_valid_blocked_except_set
            tcb_dequeue_not_queued
            tcb_sched_dequeue_valid_ready_qs)
  apply (clarsimp simp: valid_sched_def sc_tcb_sc_at_def obj_at_def)
  done
*)

lemma postpone_valid_ready_qs:
  "\<lbrace> valid_ready_qs \<rbrace>
     postpone sc_ptr
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: tcb_sched_dequeue_valid_ready_qs get_sc_obj_ref_wp)

lemma postpone_valid_release_q:
  "\<lbrace> valid_release_q and
     (\<lambda>s. \<forall> tp. sc_tcb_sc_at ((=) (Some tp)) sc_ptr s \<longrightarrow>
     st_tcb_at runnable tp s
      \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s)\<rbrace>
     postpone sc_ptr
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: tcb_release_enqueue_valid_release_q get_sc_obj_ref_wp)
  by (fastforce simp: sc_tcb_sc_at_def obj_at_def)

lemma sched_context_resume_valid_ready_qs:
  "\<lbrace> valid_ready_qs \<rbrace>
     sched_context_resume sc_opt
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_valid_ready_qs is_schedulable_wp refill_ready_wp refill_sufficient_wp
           simp: thread_get_def refill_sufficient_def)

lemma sched_context_resume_valid_release_q:
  "\<lbrace> valid_release_q\<rbrace> sched_context_resume (Some sc_ptr) \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_release_q is_schedulable_wp refill_ready_wp refill_sufficient_wp
              simp: thread_get_def)
  by (fastforce simp: active_sc_tcb_at_defs valid_release_q_def sc_tcb_sc_at_def is_schedulable_opt_def
               dest!: get_tcb_SomeD split: option.splits)

crunches tcb_release_enqueue
  for cur_thread_is_activatable[wp]: "\<lambda>s. is_activatable (cur_thread s) s"
  and switch_in_cur_domain[wp]: switch_in_cur_domain
  (wp: crunch_wps)

lemma tcb_release_enqueue_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
   tcb_release_enqueue tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. weak_valid_sched_action_2 (scheduler_action s) (kheap s) (cur_time s) (tcb_ptr # qs)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: valid_sched_release_queue_cong)
   apply (clarsimp simp: weak_valid_sched_action_def)
   apply (subgoal_tac "set qs = (fst ` {x \<in> set (zip qs r). case x of (uu_, t') \<Rightarrow> t' \<le> time} \<union>
                                 fst ` {x \<in> set (zip qs r). case x of (uu_, t') \<Rightarrow> \<not> t' \<le> time}) ")
    apply simp
   apply (clarsimp simp: image_def Collect_disj_eq[symmetric])
   apply (subgoal_tac "\<And>y. ((\<exists>b. (y, b) \<in> set (zip qs r) \<and> b \<le> time) \<or>
               (\<exists>b. (y, b) \<in> set (zip qs r) \<and> \<not> b \<le> time)) = (\<exists>b. (y, b) \<in> set (zip qs r))")
    apply (simp)
    apply (clarsimp simp: set_eq_subset subset_eq)
    apply safe[1]
     apply (fastforce elim: length_eq_pair_in_set_zip)
    apply (fastforce dest: in_set_zip1)
   apply fastforce
  apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def)
  done

lemma postpone_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. \<forall>y. sc_tcb_sc_at ((=) (Some y)) sc_ptr s \<longrightarrow> scheduler_act_not y s)\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace> "
  unfolding postpone_def valid_sched_action_def
  apply (wpsimp wp: get_sc_obj_ref_wp tcb_release_enqueue_weak_valid_sched_action)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma postpone_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. \<forall>y. sc_tcb_sc_at ((=) (Some y)) sc_ptr s \<longrightarrow> scheduler_act_not y s)\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace> "
  unfolding postpone_def
  apply (wpsimp wp: get_sc_obj_ref_wp tcb_release_enqueue_weak_valid_sched_action)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_resume_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. \<forall>y. sc_tcb_sc_at ((=) (Some y)) sc_ptr s \<longrightarrow> scheduler_act_not y s)\<rbrace>
   sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace> "
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_valid_sched_action thread_get_wp is_schedulable_wp
                 refill_ready_wp refill_sufficient_wp)
     (fastforce simp: obj_at_def is_schedulable_opt_def is_tcb
               dest!: get_tcb_SomeD split: option.splits)

lemma postpone_weak_valid_sched_action_with_invs:
  "\<lbrace>weak_valid_sched_action and sc_scheduler_act_not sc_ptr and invs\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace> "
  unfolding postpone_def
  by (wpsimp wp: get_sc_obj_ref_wp tcb_release_enqueue_weak_valid_sched_action)
     (drule (3) sc_with_tcb_prop_rev[rotated], clarsimp)

lemma postpone_valid_sched_action_with_invs:
  "\<lbrace>valid_sched_action and sc_scheduler_act_not sc_ptr and invs\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace> "
  unfolding postpone_def valid_sched_action_def
  by (wpsimp wp: get_sc_obj_ref_wp tcb_release_enqueue_weak_valid_sched_action)
     (drule (3) sc_with_tcb_prop_rev[rotated], clarsimp)

lemma sched_context_resume_valid_sched_action_with_invs:
  "\<lbrace>valid_sched_action and sc_scheduler_act_not sc_ptr and invs\<rbrace>
   sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace> "
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_sched_action_with_invs thread_get_wp is_schedulable_wp
                    refill_sufficient_wp refill_ready_wp)
  apply (frule (3) sc_with_tcb_prop_rev[rotated])
  apply (fastforce simp: obj_at_def is_schedulable_opt_def is_tcb
                  dest!: get_tcb_SomeD split: option.splits)
  done

lemma sched_context_resume_valid_sched:
  "\<lbrace>valid_sched and
    (\<lambda>s. \<forall>tp. sc_tcb_sc_at ((=) (Some tp)) sc_ptr s
              \<longrightarrow> scheduler_act_not tp s \<and>
                  bound_sc_tcb_at ((=) (Some sc_ptr)) tp s
                  )\<rbrace>
     sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_resume_def assert_opt_def)
  apply (wpsimp wp: postpone_valid_sched is_schedulable_wp refill_sufficient_wp refill_ready_wp
              simp: thread_get_def)
  by (fastforce dest!: is_schedulable_opt_Some get_tcb_SomeD
                simp: valid_sched_def obj_at_def sc_at_pred_n_def
                      not_queued_def valid_ready_qs_def etcb_defs)

lemma sched_context_resume_valid_sched_invs:
  "\<lbrace>valid_sched and sc_scheduler_act_not sc_ptr and invs\<rbrace>
     sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_resume_def assert_opt_def maybeM_def)
  apply (wpsimp wp: postpone_valid_sched_invs is_schedulable_wp refill_sufficient_wp refill_ready_wp
      simp: thread_get_def)
  apply (clarsimp simp: is_schedulable_opt_def obj_at_def get_tcb_rev valid_sched_def
                 split: option.split_asm)
  apply (drule invs_sym_refs)
  apply (frule (2) sym_ref_sc_tcb)
  apply (clarsimp simp: active_sc_tcb_at_defs)
  apply (drule sym[where t="tcb_sched_context _" and s="Some _"])
  apply (frule (2) ARM.sym_ref_tcb_sc)
  apply (clarsimp simp: active_sc_tcb_at_defs)
  done

lemma sched_context_resume_valid_sched_except_blocked: (* we could use invs *)
  "\<lbrace>valid_sched_except_blocked and
    (\<lambda>s. \<forall>sc_ptr. sc_opt = (Some sc_ptr)
       \<longrightarrow> (\<forall>tp. sc_tcb_sc_at ((=) (Some tp)) sc_ptr s
              \<longrightarrow> valid_blocked_except tp s \<and> bound_sc_tcb_at ((=) (Some sc_ptr)) tp s))\<rbrace>
     sched_context_resume sc_opt
   \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_resume_def assert_opt_def
                        refill_sufficient_def get_refills_def refill_ready_def)
  apply (wpsimp wp: postpone_valid_sched is_schedulable_wp
              simp: thread_get_def | strengthen valid_sched_imp_except_blocked)+
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def dest!: is_schedulable_opt_Some)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev)
  by (fastforce simp: not_queued_def scheduler_act_not_def valid_ready_qs_def valid_sched_action_def weak_valid_sched_action_def
                      active_sc_tcb_at_defs refill_prop_defs get_tcb_rev
               split: option.splits)

lemma postpone_valid_blocked_except_set:
  "\<lbrace>\<lambda>s. valid_blocked_except_set S s\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac tcb_opt; clarsimp)
  apply (rename_tac tptr)
  by (wpsimp wp: tcb_release_enqueue_valid_blocked_except_set tcb_sched_dequeue_valid_blocked_except_set)

lemmas postpone_valid_blocked = postpone_valid_blocked_except_set
             [of "{}", simplified]

lemma sched_context_resume_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   sched_context_resume sc_opt
   \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
    unfolding sched_context_resume_def
  by (wpsimp wp: postpone_valid_blocked_except_set is_schedulable_wp refill_sufficient_wp refill_ready_wp
           simp: thread_get_def split: if_splits)

lemmas sched_context_resume_valid_blocked = sched_context_resume_valid_blocked_except_set
             [of "{}", simplified]

crunches sched_context_resume
  for not_cur_thread[wp]: "not_cur_thread t :: det_state \<Rightarrow> _"
  and budget_ready: "\<lambda>s. P (budget_ready t s)"
  and budget_sufficient: "\<lambda>s. P (budget_sufficient t s)"
  and not_cur_thread'[wp]: "\<lambda>s. P (not_cur_thread t s)"
    (wp: crunch_wps)

context DetSchedSchedule_AI begin

crunch simple[wp]: suspend,sched_context_unbind_ntfn simple_sched_action
  (wp: maybeM_wp hoare_drop_imps)

lemma in_set_tcb_sched_dequeue:
  "t \<in> set (tcb_sched_dequeue k (ready_queues s a b)) \<Longrightarrow>
   t \<in> set (ready_queues s a b) \<and> t \<noteq> k"
 by (auto simp: tcb_sched_dequeue_def)

lemma set_thread_state_inactive_valid_ready_queues_sp:
  "\<lbrace>valid_ready_qs and tcb_at t\<rbrace>
   set_thread_state t Inactive
   \<lbrace>\<lambda>r s. (\<forall>tcb. ko_at (TCB tcb) t s \<longrightarrow>
          valid_ready_qs_2 (\<lambda>a b.
             if a = tcb_domain tcb \<and> b = tcb_priority tcb
          then tcb_sched_dequeue t (ready_queues s (tcb_domain tcb) (tcb_priority tcb))
          else ready_queues s a b)
          (cur_time s) (kheap s))\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_thread_state_act_def
                  wp: hoare_drop_imps set_scheduler_action_wp is_schedulable_wp set_object_wp)
  apply (subgoal_tac
           "\<forall>tcb. ko_at (TCB tcb) t s \<longrightarrow>
                  valid_ready_qs_2
                    (\<lambda>a b. if a = tcb_domain tcb \<and> b = tcb_priority tcb
                           then tcb_sched_dequeue t (ready_queues s (tcb_domain tcb) (tcb_priority tcb))
                           else ready_queues s a b)
                    (cur_time s)
                    (\<lambda>a. if a = t then Some (TCB (y\<lparr>tcb_state := Inactive\<rparr>)) else kheap s a)")
   apply (fastforce simp: obj_at_def is_tcb get_tcb_rev dest!: get_tcb_SomeD)
  apply (clarsimp simp: tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  apply (clarsimp simp: valid_ready_qs_def Ball_def)
  apply (intro conjI)
    (* interesting case: t is removed *)
   apply (clarsimp simp: tcb_sched_dequeue_def dest!: in_set_tcb_sched_dequeue)
   apply (drule_tac x="tcb_domain y" in spec)
   apply (drule_tac x="tcb_priority y" in spec)
   apply (clarsimp)
   apply (drule_tac x=x in spec; clarsimp)
   apply (intro conjI)
        apply (clarsimp simp: is_etcb_at'_def etcbs_of'_def)
       apply (clarsimp simp: etcb_at'_def etcbs_of'_def)
      apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
     apply (clarsimp simp: active_sc_tcb_at_kh_def active_sc_tcb_at_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def test_sc_refill_max_kh_def test_sc_refill_max_def)
     apply (subgoal_tac "scpb\<noteq> t"; fastforce)
    apply (clarsimp simp:  is_refill_sufficient_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def refill_sufficient_kh_def test_sc_refill_max_def)
    apply (subgoal_tac "scpa\<noteq> t"; fastforce?)
   apply (clarsimp simp:   is_refill_ready_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def refill_ready_kh_def test_sc_refill_max_def)
   apply (subgoal_tac "scpa\<noteq> t"; fastforce?)
    (* simple case: t is not removed *)
  apply (clarsimp)
    (* x \<noteq> t  *)  apply (subgoal_tac "x \<noteq> t")
   apply (drule_tac x="d" in spec)
   apply (drule_tac x="p" in spec; clarsimp)
   apply (drule_tac x=x in spec; clarsimp)
   apply (intro conjI)
        apply (clarsimp simp: is_etcb_at'_def etcbs_of'_def)
       apply (clarsimp simp:  etcb_at'_def etcbs_of'_def)
      apply (clarsimp simp:  st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
     apply (clarsimp simp: active_sc_tcb_at_kh_def active_sc_tcb_at_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def test_sc_refill_max_kh_def test_sc_refill_max_def)
     apply (subgoal_tac "scpb \<noteq> t"; fastforce)
    apply (clarsimp simp:  is_refill_sufficient_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def refill_sufficient_kh_def test_sc_refill_max_def)
    apply (subgoal_tac "scpa \<noteq> t"; fastforce)
   apply (clarsimp simp:   is_refill_ready_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def refill_ready_kh_def test_sc_refill_max_def)
   apply (subgoal_tac "scpa \<noteq> t"; fastforce)
    (* clean up this fact x \<noteq> t *)
  apply (fastforce simp: etcb_defs)
  done

lemma set_thread_state_not_active_helper:
  "\<lbrace>\<lambda>s. \<not> active k\<rbrace> set_thread_state t k \<lbrace>\<lambda>rv s. (st_tcb_at active t s \<longrightarrow> \<not> active_sc_tcb_at t s)\<rbrace>"
  apply (rule hoare_strengthen_post[where Q="\<lambda>rv s. (\<not>st_tcb_at active t s)"])
  apply (wpsimp simp: set_thread_state_def wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)+
  done

(* FIXME maybe move? *)
lemma weak_valid_sched_action_st_prop:
  "\<lbrakk>weak_valid_sched_action s; scheduler_action s = switch_thread t\<rbrakk> \<Longrightarrow>
       st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> budget_ready t s \<and> budget_sufficient t s"
  by (clarsimp simp: weak_valid_sched_action_def)


lemma sc_yield_from_update_valid_sched_parts:
  "\<lbrace>valid_sched_action\<rbrace> set_sc_obj_ref sc_yield_from_update a b \<lbrace>\<lambda>rv s::det_state. valid_sched_action s\<rbrace>"
  "\<lbrace>valid_blocked_except_set S\<rbrace> set_sc_obj_ref sc_yield_from_update a b \<lbrace>\<lambda>rv s::det_state. valid_blocked_except_set S s\<rbrace>"
    apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_valid_sched_action;
        fastforce simp: valid_sched_action_def weak_valid_sched_action_def active_sc_tcb_at_defs
                        sufficient_refills_def refills_capacity_def refill_prop_defs)
   apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_valid_blocked)
  done

lemma tcb_yield_to_update_in_ready_q:
  "\<lbrace>in_ready_q t\<rbrace> set_tcb_obj_ref tcb_yield_to_update a b \<lbrace>\<lambda>rv s::det_state. in_ready_q t s\<rbrace>"
   apply (wpsimp simp: set_tcb_obj_ref_def wp: update_sched_context_valid_sched_action)
  done

crunch not_in_release_q[wp]: cancel_ipc "not_in_release_q t:: det_state \<Rightarrow> _"
  (simp: crunch_simps  wp: crunch_wps tcb_release_remove_not_in_release_q')

lemma tcb_sched_dequeue_not_active:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>\<lambda>s. (st_tcb_at active t s \<longrightarrow> \<not> active_sc_tcb_at t s)\<rbrace>"
  unfolding tcb_sched_action_def
  by wpsimp

lemma tcb_sched_dequeue_valid_release_q_except[wp]:
  "tcb_sched_action tcb_sched_dequeue t' \<lbrace>valid_release_q_except t\<rbrace>"
  unfolding tcb_sched_action_def
  by wpsimp

lemma suspend_valid_sched:
  "\<lbrace>valid_objs and scheduler_act_not t and valid_sched and (\<lambda>s. sym_refs (state_refs_of s)) and tcb_at t\<rbrace>
      suspend t
   \<lbrace>\<lambda>rv. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: suspend_def maybeM_def valid_sched_def)
  apply (wp tcb_release_remove_valid_release_q_except | wpc)+
        apply (wpsimp wp: tcb_release_remove_valid_blocked_except_set_remove)
       apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs' hoare_vcg_conj_lift tcb_sched_dequeue_valid_blocked_except_set_remove
                         hoare_vcg_all_lift hoare_vcg_imp_lift)
         apply (rule hoare_pre_cont)
       apply wpsimp
      apply (wpsimp wp: set_thread_state_inactive_valid_ready_queues_sp
                        set_thread_state_valid_release_q_except
                        set_thread_state_act_not_valid_sched_action)
      apply (rule_tac Q="\<lambda>_ s. valid_blocked_except_set {t} s \<and> \<not> st_tcb_at runnable t s \<and>  valid_idle_etcb s"
                  in hoare_strengthen_post[rotated])
       apply (clarsimp simp: runnable_eq_active)
      apply (wpsimp wp: sts_st_tcb_at_pred_False set_thread_state_valid_blocked_except_set_const)
     apply (wpsimp wp: set_tcb_yield_to_valid_sched_action set_tcb_yield_to_valid_ready_qs tcb_yield_to_update_in_ready_q)
     apply (wpsimp wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q set_sc_obj_ref_ct_in_cur_domain
                       sc_yield_from_update_valid_sched_parts)
    apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp)
   apply (rule hoare_strengthen_post[where Q="\<lambda>r. valid_sched and scheduler_act_not t and tcb_at t"])
    apply (wpsimp wp: cancel_ipc_valid_sched)
   apply (clarsimp simp: valid_sched_def obj_at_def is_tcb split: option.splits)
   apply (fastforce simp: valid_ready_qs_def valid_release_q_def active_sc_tcb_at_defs
                          in_queue_2_def refill_prop_defs sufficient_refills_def refills_capacity_def
                   split: option.splits)
  apply (wpsimp wp: cancel_ipc_valid_sched)
  apply (clarsimp simp: valid_sched_def)
  done

lemma tcb_sched_context_update_None_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except ref and not_queued ref and not_in_release_q ref and scheduler_act_not ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref None
   \<lbrace>\<lambda>_. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                 set_tcb_sched_context_valid_release_q_not_queued
                 set_tcb_sched_context_valid_blocked_except_None
                 set_tcb_sched_context_valid_sched_action_act_not)

lemma sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and
   (\<lambda>s. \<forall>sc. (\<exists>n. ko_at (SchedContext sc n) sc_ptr s) \<longrightarrow> (\<forall>y. sc_tcb sc = Some y \<longrightarrow> scheduler_act_not y s))\<rbrace>
   sched_context_unbind_tcb sc_ptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_unbind_tcb_def
  apply (wpsimp wp: tcb_sched_context_update_None_valid_sched tcb_release_remove_valid_blocked_except2
                    tcb_sched_dequeue_valid_ready_qs tcb_sched_dequeue_valid_blocked_except_set tcb_dequeue_not_queued
                    reschedule_required_valid_blocked_except_set)
  apply (clarsimp simp: valid_sched_def)
  done

lemma maybe_sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and
   (\<lambda>s. \<forall>sc_ptr. bound_sc_tcb_at (\<lambda>x. x = Some sc_ptr) tcb_ptr s \<longrightarrow>
                 (\<forall>sc. (\<exists>n. ko_at (SchedContext sc n) sc_ptr s) \<longrightarrow>
                        (\<forall>y. sc_tcb sc = Some y \<longrightarrow>
                             scheduler_act_not y s)))\<rbrace>
   maybe_sched_context_unbind_tcb tcb_ptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_sched_context_unbind_tcb_def
  apply (wpsimp wp: sched_context_unbind_tcb_valid_sched get_tcb_obj_ref_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma sched_context_unbind_all_tcbs_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
   sched_context_unbind_all_tcbs sc_ptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_unbind_all_tcbs_def
  by (wpsimp wp: sched_context_unbind_tcb_valid_sched)

lemma sched_context_unbind_reply_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_unbind_reply sc_ptr \<lbrace>\<lambda>yb. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_unbind_reply_def
  by wpsimp

lemma set_sc_obj_ref_sc_at_pred_n_no_change:
  "\<forall>sc. P (proj sc) \<longrightarrow> P (proj (f (\<lambda>y. val) sc)) \<Longrightarrow>
   set_sc_obj_ref f scptr val \<lbrace>sc_at_pred_n Q proj P scptr'\<rbrace>"
 unfolding set_sc_obj_ref_def
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: sc_at_pred_n_def obj_at_def)

lemma sched_context_unbind_ntfn_sc_tcb_sc_at[wp]:
  "sched_context_unbind_ntfn scptr \<lbrace>sc_tcb_sc_at Q scptr\<rbrace>"
  unfolding sched_context_unbind_ntfn_def
 by (wpsimp wp: set_sc_obj_ref_sc_at_pred_n_no_change simp: get_sc_obj_ref_def)

lemma sched_context_unbind_reply_sc_tcb_sc_at[wp]:
  "sched_context_unbind_reply scptr \<lbrace>sc_tcb_sc_at Q scptr\<rbrace>"
  unfolding sched_context_unbind_reply_def
 by (wpsimp wp: set_sc_obj_ref_sc_at_pred_n_no_change simp: get_sc_obj_ref_def)

lemma sched_context_unbind_all_tcbs_sc_tcb_sc_at_None[wp]:
  "\<lbrace>K (scptr \<noteq> idle_sc_ptr)\<rbrace>
   sched_context_unbind_all_tcbs scptr
   \<lbrace>\<lambda>rv. sc_tcb_sc_at (\<lambda>x. x = None) scptr\<rbrace>"
  unfolding sched_context_unbind_all_tcbs_def sched_context_unbind_tcb_def
  apply (wpsimp wp: update_sched_context_wp set_object_wp
              simp:  set_sc_obj_ref_def set_tcb_obj_ref_def)
         apply (rule_tac Q="\<top>\<top>" in hoare_strengthen_post[rotated])
          apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
         apply (wpsimp+)[7]
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  done

crunch sc_tcb_sc_at_inv'_none[wp]: do_machine_op "\<lambda>s. sc_tcb_sc_at P scp s"
  (simp: crunch_simps split_def sc_tcb_sc_at_def wp: crunch_wps hoare_drop_imps)

crunch sc_tcb_sc_at_inv'_none[wp]: store_word_offs "\<lambda>s. sc_tcb_sc_at P scp s"
  (simp: crunch_simps split_def wp: crunch_wps hoare_drop_imps ignore: do_machine_op)

lemma set_mrs_sc_tcb_sc_at_inv'_none[wp]:
  "set_mrs thread buf msgs \<lbrace> \<lambda>s. sc_tcb_sc_at P scp s\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
         simp: split_def set_object_def zipWithM_x_mapM)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def dest!: get_tcb_SomeD)

lemma set_message_info_sc_tcb_sc_at_inv_none'[wp]:
  "set_message_info thread info \<lbrace> \<lambda>s. sc_tcb_sc_at P scp s\<rbrace>"
  apply (simp add: set_message_info_def)
  by (wpsimp wp: get_object_wp hoare_drop_imp split_del: if_split
          simp: split_def as_user_def set_object_def)

lemma sched_context_update_consumed_sc_tcb_sc_at_inv'_none[wp]:
  "sched_context_update_consumed sp \<lbrace> \<lambda>s. sc_tcb_sc_at P scp s\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp wp: get_object_wp get_sched_context_wp hoare_drop_imp split_del: if_split
           simp: split_def update_sched_context_def set_object_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma set_consumed_sc_tcb_sc_at_inv'_none[wp]:
  "set_consumed sp buf \<lbrace> \<lambda>s. sc_tcb_sc_at P scp s\<rbrace>"
  apply (simp add: set_consumed_def)
  by (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
           simp: split_def set_message_info_def as_user_def set_mrs_def set_object_def
                 sc_tcb_sc_at_def zipWithM_x_mapM)

lemma sched_context_unbind_yield_from_sc_tcb_sc_at[wp]:
  "sched_context_unbind_yield_from scptr \<lbrace>sc_tcb_sc_at P scptr\<rbrace>"
  unfolding sched_context_unbind_yield_from_def
  by (wpsimp simp: complete_yield_to_def wp: set_sc_obj_ref_sc_at_pred_n_no_change hoare_drop_imps)

lemma set_sc_refill_max_valid_sched[wp]:
  "\<lbrace>valid_sched and
    (\<lambda>s. \<forall>t. bound_sc_tcb_at (\<lambda>x. x = Some ref) t s \<longrightarrow>
             (not_queued t s \<and> not_in_release_q t s \<and> scheduler_action s \<noteq> switch_thread t))\<rbrace>
   set_sc_obj_ref sc_refill_max_update ref 0
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q valid_idle_etcb_lift
                   set_sc_obj_ref_ct_in_cur_domain set_sc_obj_ref_valid_blocked set_sc_obj_ref_valid_sched_action)

lemma fast_finalise_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
     and valid_ep_q and valid_ntfn_q and (\<lambda>s. \<exists>slot. cte_wp_at ((=) cap) slot s)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  apply (cases cap; clarsimp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_valid_sched, intro conjI; clarsimp)
    apply wpsimp
   apply (wpsimp wp: cancel_ipc_valid_sched get_simple_ko_wp
                     reply_remove_valid_sched gts_wp)
  apply (subgoal_tac "valid_objs s \<and> sym_refs (state_refs_of s)", clarsimp)
    apply (frule(2) st_tcb_reply_state_refs; clarsimp simp: pred_tcb_at_eq_commute)
    apply (clarsimp simp: pred_tcb_at_def reply_tcb_reply_at_def obj_at_def)
   apply (intro conjI; clarsimp)
  apply (rename_tac scptr x)
  apply (wpsimp wp: )
      apply (rule_tac Q="\<lambda>ya. invs and sc_tcb_sc_at (\<lambda>x. x = None) scptr"
                             in hoare_strengthen_post[rotated])
       apply clarsimp
       apply (simp add: sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl invs_sym_refs])
       apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
      apply ((wpsimp wp: Finalise_AI_2.sched_context_unbind_yield_from_invs)+)[4]
  apply (clarsimp split: if_splits)
  apply (fastforce simp: invs_def valid_state_def cap_range_def dest!: valid_global_refsD)
  done

lemma cap_delete_one_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
     and valid_ep_q and valid_ntfn_q\<rbrace>
   cap_delete_one (a, b)
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: fast_finalise_valid_sched get_cap_wp, fastforce)

lemma deleting_irq_handler_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
     and valid_ep_q and valid_ntfn_q\<rbrace>
   deleting_irq_handler irq
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by (wpsimp wp: cap_delete_one_valid_sched)

lemma unbind_from_sc_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
   unbind_from_sc tcb_ptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding unbind_from_sc_def
  by (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift maybeM_wp sched_context_unbind_tcb_valid_sched)

crunch simple_sched_action[wp]: unbind_notification simple_sched_action
  (simp: crunch_simps wp: crunch_wps)

(* precondition could be weaker (invs > (sym_refs and valid_objs)) but
   this is much simpler to prove *)
lemma finalise_cap_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and simple_sched_action and valid_cap cap and (\<lambda>s. \<exists>slot. cte_wp_at ((=) cap) slot s)
    and valid_ep_q and valid_ntfn_q and (\<lambda>s. cap \<noteq> ThreadCap idle_thread_ptr)\<rbrace>
   finalise_cap cap param_b
   \<lbrace>\<lambda>_. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  supply if_splits [split del]
  apply (case_tac cap; (solves \<open>wpsimp\<close>)?; simp)
       apply (wpsimp wp: cancel_all_ipc_valid_sched cancel_ipc_valid_sched get_simple_ko_wp
                   simp: invs_valid_objs
                  split: if_splits)
      apply (wpsimp wp: cancel_ipc_valid_sched reply_remove_valid_sched gts_wp get_simple_ko_wp
                 split: if_splits)
     apply (wpsimp wp: cancel_ipc_valid_sched reply_remove_valid_sched gts_wp get_simple_ko_wp
                split: if_splits)
     apply (safe; clarsimp)
     apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_eq_commute)
     apply (subgoal_tac "\<exists>reply. (kheap s xa = Some (Reply reply) \<and> reply_tcb reply = Some x)")
      apply (clarsimp simp: runnable_def st_tcb_at_def obj_at_def)
     apply (rule_tac st_tcb_reply_state_refs[OF invs_valid_objs invs_sym_refs];
            clarsimp simp: pred_tcb_at_eq_commute)
    apply (wpsimp wp: suspend_valid_sched)
      apply (rule_tac Q="\<lambda>ya. valid_sched and invs and scheduler_act_not x7 and tcb_at x7"
                      in hoare_strengthen_post)
       apply (wpsimp wp: unbind_from_sc_valid_sched)
      apply fastforce
     apply (wpsimp wp: unbind_notification_invs split: if_splits)
    apply (clarsimp simp: valid_cap_def split: if_splits)
   apply (rename_tac scptr x)
   apply wpsimp
       apply (rule_tac Q="\<lambda>ya. invs and sc_tcb_sc_at (\<lambda>x. x = None) scptr"
                       in hoare_strengthen_post[rotated])
        apply clarsimp
        apply (simp add: sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl invs_sym_refs])
        apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
       apply ((wpsimp wp: Finalise_AI_2.sched_context_unbind_yield_from_invs)+)[4]
   apply (clarsimp split: if_splits)
   apply (fastforce simp: invs_def valid_state_def cap_range_def dest!: valid_global_refsD)
  apply (wpsimp wp: deleting_irq_handler_valid_sched)
  done

end

crunch simple_sched_action[wp]: cap_swap_for_delete, cap_insert simple_sched_action

lemma store_word_offs_cur_sc_chargeable[wp]:
  "store_word_offs a b c \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding store_word_offs_def
  by (wpsimp wp: set_object_wp)

lemma set_mrs_cur_sc_chargeable[wp]:
  "set_mrs thread buf msgs \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding set_mrs_def
  apply (wpsimp wp: set_object_wp zipWithM_x_inv')
  by (clarsimp simp: cur_sc_chargeable_def bound_sc_tcb_at_kh_def obj_at_kh_def st_tcb_at_kh_def
                 dest!: get_tcb_SomeD, fastforce)

context DetSchedSchedule_AI begin

crunches
  empty_slot, unbind_maybe_notification, sched_context_maybe_unbind_ntfn,
  sched_context_unbind_yield_from, sched_context_unbind_reply, finalise_cap
  for simple_sched_action[wp]: simple_sched_action
  (wp: crunch_wps simp: crunch_simps)

lemma valid_sched_implies_valid_ipc_qs:
  "valid_sched s \<Longrightarrow> valid_ep_q s"
  "valid_sched s \<Longrightarrow> valid_ntfn_q s"
  sorry (* valid_sched implies valid_ipc_qs *)

lemma rec_del_valid_sched:
 "\<lbrace>valid_sched and simple_sched_action and invs and valid_rec_del_call args
        and (\<lambda>s. \<not> exposed_rdcall args
               \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
        and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                       \<not> cap_removeable cap sl
                       \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                  | _ \<Rightarrow> True)\<rbrace>
  rec_del args
  \<lbrace>\<lambda>rv. valid_sched ::det_state \<Rightarrow> _\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_post_impErr)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs''[where Q="valid_sched and simple_sched_action"])
         apply wpsimp+
       apply (clarsimp simp: invs_valid_objs cte_wp_valid_cap
                             valid_sched_implies_valid_ipc_qs)
       apply (frule(1) valid_global_refsD[OF invs_valid_global_refs _ idle_global])
       apply (clarsimp dest!: invs_valid_idle simp: valid_idle_def cap_range_def)
      apply (wpsimp wp: preemption_point_inv')+
  done

lemma rec_del_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wpsimp wp: rec_del_preservation preemption_point_inv' finalise_cap_simple_sched_action)

lemma arch_post_cap_deletion_scheduler_act_sane[wp]:
  "arch_post_cap_deletion x \<lbrace>scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (wps ARM.arch_post_cap_deletion_cur_thread)
  apply wpsimp+
  done

crunch scheduler_act_sane[wp]: cap_swap_for_delete, empty_slot "scheduler_act_sane :: det_state \<Rightarrow> _"
  (simp: unless_def wp: maybeM_inv ignore: set_object)

lemma possible_switch_to_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and (\<lambda>s. scheduler_action s = resume_cur_thread \<longrightarrow> not_in_release_q t s \<longrightarrow> t \<noteq> cur_thread s)\<rbrace>
   possible_switch_to t
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: set_scheduler_action_wp get_tcb_obj_ref_wp)
  by (clarsimp simp: scheduler_act_sane_def)

lemma possible_switch_to_scheduler_act_sane':
  "\<lbrace>scheduler_act_sane and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   possible_switch_to t
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: set_scheduler_action_wp get_tcb_obj_ref_wp)
  by (clarsimp simp: scheduler_act_sane_def)

lemma restart_thread_if_no_fault_scheduler_act_sane[wp]:
 "\<lbrace>scheduler_act_sane and (\<lambda>s. xa \<noteq> cur_thread s) and tcb_at xa\<rbrace>
  restart_thread_if_no_fault xa
  \<lbrace>\<lambda>_. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: set_thread_state_def set_thread_state_act_def
               wp: possible_switch_to_scheduler_act_sane set_scheduler_action_wp is_schedulable_wp
                   set_object_wp thread_get_wp
                   hoare_vcg_imp_lift' )

lemma tcb_sched_enqueue_ct_not_queued:
  "\<lbrace> ct_not_queued and (\<lambda>s. cur \<noteq> cur_thread s)\<rbrace>
   tcb_sched_action tcb_sched_enqueue cur
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  by (fastforce simp: not_queued_def tcb_sched_enqueue_def)

lemma possible_switch_to_ct_not_queued:
  "\<lbrace>ct_not_queued and (\<lambda>s. t \<noteq> cur_thread s) and scheduler_act_sane\<rbrace> possible_switch_to t \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: tcb_sched_enqueue_ct_not_queued)
  done

lemma restart_thread_if_no_fault_ct_not_queued[wp]:
 "\<lbrace>ct_not_queued and scheduler_act_sane and (\<lambda>s. xa \<noteq> cur_thread s) and tcb_at xa\<rbrace>
  restart_thread_if_no_fault xa
  \<lbrace>\<lambda>_. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: set_thread_state_def set_thread_state_act_def
               wp: possible_switch_to_ct_not_queued set_scheduler_action_wp is_schedulable_wp
                   set_object_wp thread_get_wp
                   hoare_vcg_imp_lift' )

crunches cancel_all_ipc
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma cancel_all_ipc_scheduler_act_sane[wp]:
 "\<lbrace>scheduler_act_sane and valid_ep_q:: det_state \<Rightarrow> _\<rbrace>
  cancel_all_ipc epptr
  \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding cancel_all_ipc_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ep=IdleEP"; simp?)
   apply wpsimp
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and scheduler_act_sane and valid_ep_q) s" in hoare_weaken_pre)
     apply (rule hoare_seq_ext[OF _ get_epq_sp])
     apply wpsimp
       apply (rule_tac Q="\<lambda>_. scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> tcb_at t x \<and> t \<noteq> cur_thread x)" in hoare_strengthen_post)
        apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
         prefer 2
         apply (rule subset_refl, clarsimp, clarsimp)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (clarsimp simp: valid_ep_q_def obj_at_def)
     apply (drule_tac x=epptr in spec)
     apply clarsimp
     apply (drule_tac x=x in bspec, simp)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply assumption
   apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and scheduler_act_sane and valid_ep_q) s" in hoare_weaken_pre)
    apply (rule hoare_seq_ext[OF _ get_epq_sp])
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> tcb_at t x \<and> t \<noteq> cur_thread x)" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
        prefer 2
        apply (rule subset_refl, clarsimp, clarsimp)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (clarsimp simp: valid_ep_q_def obj_at_def)
    apply (drule_tac x=epptr in spec)
    apply clarsimp
    apply (drule_tac x=x in bspec, simp)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply assumption
  apply fastforce
  done


crunches update_time_stamp
  for release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"

lemma update_time_stamp_is_refill_sufficient[wp]:
  "update_time_stamp \<lbrace>is_refill_sufficient scp k\<rbrace>"
  unfolding update_time_stamp_def
  apply (wpsimp simp: do_machine_op_def)
  apply (clarsimp simp: budget_sufficient_defs sc_at_pred_n_def  split: option.splits)
  done

crunches update_time_stamp
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T t  s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and sc_at_pred_n[wp]: "\<lambda>s. Q (sc_at_pred_n N p P t s)"

lemma tcb_ready_time_cur_time_update:
  "P (tcb_ready_time t (s\<lparr>cur_time := new\<rparr>)) = P (tcb_ready_time t s)"
  by (clarsimp simp: tcb_ready_time_def get_tcb_def dest!: get_tcb_SomeD split: option.splits)

crunches update_time_stamp
  for tcb_ready_time[wp]: "\<lambda>s. P (tcb_ready_time t s)"
  (wp: crunch_wps simp: crunch_simps tcb_ready_time_cur_time_update)

lemma update_time_stamp_ct_not_in_queues[wp]:
 "update_time_stamp \<lbrace>ct_not_in_release_q\<rbrace>"
 "update_time_stamp \<lbrace>ct_not_queued\<rbrace>"
  unfolding update_time_stamp_def
  by (wpsimp simp: | wps)+

lemma update_time_stamp_active_sc_tcb_at[wp]:
 "update_time_stamp \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (rule bool_to_bool_cases[of P]; wpsimp)
   apply (rule_tac Q="\<lambda>_ s. \<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and> sc_at_pred sc_refill_max (\<lambda>x. 0 < x ) scp s"
    in hoare_strengthen_post)
    apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_imp_lift)
    apply (clarsimp simp: active_sc_tcb_at_defs sc_at_pred_n_def split: option.splits)
    apply (case_tac y; simp)
   apply (fastforce simp: active_sc_tcb_at_defs sc_at_pred_n_def split: option.splits)
  apply (rule_tac Q="\<lambda>_ s. \<forall>scp. ~ bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<or> ~sc_at_pred sc_refill_max (\<lambda>x. 0 < x ) scp s"
   in hoare_strengthen_post)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
   apply (clarsimp simp: active_sc_tcb_at_defs sc_at_pred_n_def split: option.splits)
  apply (clarsimp simp: active_sc_tcb_at_defs sc_at_pred_n_def split: option.splits)
  apply (case_tac x2; simp)
  done

lemma update_time_stamp_budget_sufficient[wp]:
 "update_time_stamp \<lbrace>budget_sufficient t\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and> sc_at_pred sc_refills (\<lambda>x. sufficient_refills 0 x ) scp s"
   in hoare_strengthen_post)
   apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_imp_lift)
   apply (clarsimp simp: budget_sufficient_defs sc_at_pred_n_def split: option.splits)
  apply (clarsimp simp: budget_sufficient_defs sc_at_pred_n_def split: option.splits)
  done

lemma update_time_stamp_bound_cur_sc_tcb[wp]:
  "update_time_stamp \<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s\<rbrace>"
  apply (rule hoare_lift_Pf[where f=cur_thread])
  apply (rule hoare_lift_Pf[where f=cur_sc])
  by wpsimp+

lemma update_time_stamp_cur_sc_chargeable[wp]:
  "update_time_stamp \<lbrace>cur_sc_chargeable\<rbrace>"
  by (wpsimp simp: cur_sc_chargeable_def2 wp: hoare_vcg_imp_lift hoare_vcg_all_lift | wps)+

crunches update_time_stamp
  for obj_at[wp]: "\<lambda>(s::det_state). Q (obj_at P t s)"

lemma dmo_getCurrentTime_sp[wp]:
  "do_machine_op getCurrentTime \<lbrace>P\<rbrace> \<Longrightarrow>
   \<lbrace>valid_machine_time and P :: det_state \<Rightarrow> _\<rbrace>
   do_machine_op getCurrentTime
   \<lbrace>\<lambda>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1) \<and>  P s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. P s \<and> ((cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1))" in hoare_strengthen_post)
  apply (wp hoare_vcg_conj_lift)
  apply (rule dmo_getCurrentTime_vmt_sp)
  by simp+

lemma update_time_stamp_is_refill_ready[wp]:
 "\<lbrace>valid_machine_time and is_refill_ready scp 0 :: det_state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_. is_refill_ready scp 0\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="valid_machine_time and (is_refill_ready scp 0 and
                     (\<lambda>s. cur_time s = prev_time))" in hoare_weaken_pre[rotated])
   apply clarsimp
  apply (rule_tac hoare_seq_ext[OF _ dmo_getCurrentTime_sp])
   apply (wpsimp simp: )
   apply (clarsimp simp: is_refill_ready_def obj_at_def)
   apply (rule_tac b="cur_time s + kernelWCET_ticks" in order.trans, simp)
   apply (rule word_plus_mono_left, simp)
   apply (subst olen_add_eqv)
   apply (subst add.commute)
   apply (rule no_plus_overflow_neg)
   apply (erule minus_one_helper5[rotated])
   using kernelWCET_ticks_non_zero
   apply fastforce
  apply wpsimp
  done

lemma update_time_stamp_budget_ready[wp]:
 "\<lbrace>budget_ready t and valid_machine_time :: det_state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and>
                                 is_refill_ready scp 0 s"
   in hoare_strengthen_post)
   apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_imp_lift)
   apply (clarsimp simp: budget_ready_defs sc_at_pred_n_def split: option.splits)
  apply (clarsimp simp: budget_sufficient_defs sc_at_pred_n_def split: option.splits)
  done

lemma update_time_stamp_valid_ipc_queues[wp]:
  "\<lbrace>valid_ep_q and valid_machine_time\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>valid_ntfn_q and valid_machine_time\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. valid_ntfn_q ::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_ntfn_q_lift_pre_conj[where R=valid_machine_time]
                 valid_ep_q_lift_pre_conj[where R=valid_machine_time]
                 hoare_vcg_disj_lift)+

lemma cancel_all_signals_scheduler_act_sane[wp]:
 "\<lbrace>scheduler_act_sane and valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>
  cancel_all_signals f
  \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding cancel_all_signals_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Notification ntfn) f and scheduler_act_sane and valid_ntfn_q) s" in hoare_weaken_pre[rotated])
     apply assumption
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. scheduler_act_sane and (\<lambda>s. \<forall>x \<in> set x2. x \<noteq> (cur_thread s))" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp[where xs = t and S = "set t" for t, simplified])
        apply (wpsimp wp: possible_switch_to_scheduler_act_sane')+
       apply fastforce
      apply fastforce
     apply (wpsimp wp: )+
    apply (clarsimp simp: valid_ntfn_q_def obj_at_def)
    apply (drule_tac x=f in spec, fastforce simp: ntfn_queue_def)
   apply wpsimp
  apply clarsimp
  done

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn, cancel_ipc, suspend
  for scheduler_act_sane[wp]: "scheduler_act_sane :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma misc_arch_scheduler_act_sane[wp]:
  "prepare_thread_delete x \<lbrace>scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  "arch_finalise_cap z b \<lbrace>scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_weaken_pre, wps | wpsimp)+

crunches complete_yield_to, sched_context_unbind_tcb, unbind_from_sc, unbind_notification,
         sched_context_unbind_yield_from, sched_context_unbind_reply, sched_context_unbind_ntfn,
         sched_context_unbind_all_tcbs
  for scheduler_act_sane[wp]: "scheduler_act_sane :: det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_inv)

lemma fast_finalise_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   fast_finalise cap x
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap)
               apply ((wpsimp wp: gts_wp get_simple_ko_wp | intro conjI impI)+)
  done

lemma deleting_irq_handler_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   deleting_irq_handler y
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by (wpsimp simp: cap_delete_one_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma finalise_cap_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   finalise_cap cap param_b
   \<lbrace>\<lambda>_. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap)
               apply ((wpsimp wp: gts_wp get_simple_ko_wp | intro conjI impI)+)
  done

lemma cancel_all_ipc_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ep_q\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>_. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  unfolding cancel_all_ipc_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ep=IdleEP"; simp?)
   apply wpsimp
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and ct_not_queued and scheduler_act_sane and valid_ep_q) s" in hoare_weaken_pre)
     apply (rule hoare_seq_ext[OF _ get_epq_sp])
     apply wpsimp
       apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> tcb_at t x \<and> t \<noteq> cur_thread x)" in hoare_strengthen_post)
        apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
         prefer 2
         apply (rule subset_refl, clarsimp, clarsimp)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (clarsimp simp: valid_ep_q_def obj_at_def)
     apply (drule_tac x=epptr in spec)
     apply clarsimp
     apply (drule_tac x=x in bspec, simp)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply assumption
   apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and ct_not_queued and scheduler_act_sane and valid_ep_q) s" in hoare_weaken_pre)
    apply (rule hoare_seq_ext[OF _ get_epq_sp])
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> tcb_at t x \<and> t \<noteq> cur_thread x)" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
        prefer 2
        apply (rule subset_refl, clarsimp, clarsimp)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (clarsimp simp: valid_ep_q_def obj_at_def)
    apply (drule_tac x=epptr in spec)
    apply clarsimp
    apply (drule_tac x=x in bspec, simp)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply assumption
  apply fastforce
  done

lemma cancel_all_signals_ct_not_queued[wp]:
 "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>
  cancel_all_signals f
  \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  unfolding cancel_all_signals_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Notification ntfn) f and ct_not_queued and scheduler_act_sane and valid_ntfn_q) s" in hoare_weaken_pre[rotated])
     apply assumption
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>s. \<forall>x \<in> set x2. x \<noteq> (cur_thread s))" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp[where xs = t and S = "set t" for t, simplified])
        apply (wpsimp wp: possible_switch_to_scheduler_act_sane' possible_switch_to_ct_not_queued)+
       apply fastforce
      apply fastforce
     apply (wpsimp wp: )+
    apply (clarsimp simp: valid_ntfn_q_def obj_at_def)[1]
    apply (drule_tac x=f in spec, fastforce simp: ntfn_queue_def)
   apply wpsimp
  apply clarsimp
  done

lemma tcb_sched_dequeue_ct_not_queued:
  "tcb_sched_action tcb_sched_dequeue x \<lbrace>ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp tcb_dequeue_not_queued_gen, simp)

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn, cancel_ipc
  for ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

crunches reply_remove, suspend, complete_yield_to, sched_context_unbind_tcb, unbind_notification,
         sched_context_unbind_yield_from, sched_context_unbind_reply, sched_context_unbind_ntfn,
         sched_context_unbind_all_tcbs
  for ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp tcb_sched_dequeue_ct_not_queued simp: crunch_simps ignore: tcb_sched_action)

lemma misc_arch_ct_queue_lemmas[wp]:
  "arch_post_cap_deletion x \<lbrace>ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  "prepare_thread_delete x2 \<lbrace>ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  "arch_finalise_cap a b \<lbrace>ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace> "
  "arch_post_cap_deletion x \<lbrace>ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  "prepare_thread_delete x2 \<lbrace>ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  "arch_finalise_cap a b \<lbrace>ct_not_queued :: det_state \<Rightarrow> _\<rbrace> "
  apply (rule hoare_weaken_pre, wps, wpsimp, simp)+
  done

crunches empty_slot
  for ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma fast_finalise_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace> fast_finalise cap x \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap)
               apply ((wpsimp wp: gts_wp get_simple_ko_wp | intro conjI impI)+)
  done

lemma deleting_irq_handler_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace>
   deleting_irq_handler y
   \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by (wpsimp simp: cap_delete_one_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma unbind_from_sc_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace>
   unbind_from_sc x7
   \<lbrace>\<lambda>_. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  unfolding unbind_from_sc_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)

lemma finalise_cap_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace>
   finalise_cap cap param_b
   \<lbrace>\<lambda>_. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap)
               apply ((wpsimp wp: gts_wp get_simple_ko_wp | intro conjI impI)+)
  done

lemma set_sc_obj_ref_cur_sc_chargeable_const:
  "(\<And>sc.  sc_tcb (f (\<lambda>y. val) sc) = sc_tcb sc ) \<Longrightarrow>
   set_sc_obj_ref f scp val \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_wp)
  apply (clarsimp simp: cur_sc_chargeable_def obj_at_def pred_tcb_at_def
                        bound_sc_tcb_at_kh_def obj_at_kh_def st_tcb_at_kh_def, fastforce)
  done

lemma set_tcb_obj_ref_cur_sc_chargeable_const:
  "(\<And>t. tcb_sched_context (f (\<lambda>y. val) t) =  tcb_sched_context t \<and>
         tcb_state (f (\<lambda>y. val) t) =  tcb_state t) \<Longrightarrow>
   set_tcb_obj_ref f tptr val \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  apply (fastforce simp: cur_sc_chargeable_def obj_at_def pred_tcb_at_def
                         bound_sc_tcb_at_kh_def obj_at_kh_def st_tcb_at_kh_def
                  dest!: get_tcb_SomeD)
  done

lemma update_sched_context_cur_sc_chargeable_const:
  "(\<And>x. sc_tcb (f x) = sc_tcb x) \<Longrightarrow>
   update_sched_context ptr f \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: cur_sc_chargeable_def obj_at_def pred_tcb_at_def
                         bound_sc_tcb_at_kh_def obj_at_kh_def st_tcb_at_kh_def, fastforce
                  dest!: get_tcb_SomeD)
  done

lemma thread_set_cur_sc_chargeable_const:
  "(\<And>x. tcb_sched_context (f x) = tcb_sched_context x \<and>
         tcb_state (f x) = tcb_state x) \<Longrightarrow>
   thread_set f x2 \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (simp add: cur_sc_chargeable_def2)
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp dest!: get_tcb_SomeD
                   simp: obj_at_def pred_tcb_at_def sc_at_pred_def)
  apply (case_tac "cur_thread s = x2"; simp, fastforce)
  done

lemmas misc_cur_sc_chargeable_const = set_sc_obj_ref_cur_sc_chargeable_const
                set_tcb_obj_ref_cur_sc_chargeable_const
                thread_set_cur_sc_chargeable_const
                update_sched_context_cur_sc_chargeable_const

lemma update_sk_obj_ref_cur_sc_chargeable:
  "inj C \<Longrightarrow> (\<And>x y. C x \<noteq> TCB y) \<Longrightarrow> (\<And>x y n. C x \<noteq> SchedContext y n) \<Longrightarrow>
   update_sk_obj_ref C f ref new
   \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding update_sk_obj_ref_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (clarsimp simp: cur_sc_chargeable_def2 cur_sc_chargeable_def
                        obj_at_def pred_tcb_at_def is_sc_obj_def
                        bound_sc_tcb_at_kh_def obj_at_kh_def simple_obj_at_def st_tcb_at_kh_def, fastforce)
  done

lemma set_simple_ko_cur_sc_chargeable:
  "inj C \<Longrightarrow> (\<And>x y. C x \<noteq> TCB y) \<Longrightarrow> (\<And>x y n. C x \<noteq> SchedContext y n) \<Longrightarrow>
   set_simple_ko C ref new
   \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding update_sk_obj_ref_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (clarsimp simp: cur_sc_chargeable_def2 cur_sc_chargeable_def
                        obj_at_def pred_tcb_at_def is_sc_obj_def
                        bound_sc_tcb_at_kh_def obj_at_kh_def simple_obj_at_def st_tcb_at_kh_def, fastforce)
  done

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn, unbind_notification,
         sched_context_unbind_reply, sched_context_unbind_ntfn
  for cur_sc_chargeable[wp]: cur_sc_chargeable
  (ignore: set_tcb_obj_ref set_sc_obj_ref
       wp: misc_cur_sc_chargeable_const crunch_wps)

lemma sched_context_update_consumed_cur_sc_chargeable[wp]:
  "sched_context_update_consumed x \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding sched_context_update_consumed_def cur_sc_chargeable_def2
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def sc_at_pred_def obj_at_def
                 dest!: get_tcb_SomeD, fastforce)
  done

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn, unbind_notification,
         sched_context_unbind_reply, sched_context_unbind_ntfn, set_message_info, set_consumed
  for cur_sc_chargeable[wp]: cur_sc_chargeable
  (ignore: set_tcb_obj_ref set_sc_obj_ref
       wp: misc_cur_sc_chargeable_const crunch_wps)

lemma complete_yield_to_cur_sc_chargeable[wp]:
  "complete_yield_to x \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding complete_yield_to_def
  by (wpsimp wp: misc_cur_sc_chargeable_const hoare_drop_imp)

crunches tcb_release_remove, tcb_sched_action, reschedule_required
  for cur_sc_chargeable[wp]: cur_sc_chargeable
  (wp: crunch_wps)

lemma sched_context_unbind_tcb_cur_sc_chargeable[wp]:
  "sched_context_unbind_tcb xb \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding sched_context_unbind_tcb_def
  apply (wp)
  apply (simp add: cur_sc_chargeable_def2)
  apply (wpsimp wp: set_sc_obj_ref_wp)
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (rule_tac Q="\<lambda>_. cur_sc_chargeable" in hoare_strengthen_post[rotated])
  apply (clarsimp simp: cur_sc_chargeable_def2 obj_at_def pred_tcb_at_def sc_at_pred_def, fastforce)
  apply wpsimp+
  done

crunches sched_context_unbind_yield_from, sched_context_unbind_all_tcbs, unbind_from_sc
  for cur_sc_chargeable[wp]: cur_sc_chargeable
  (ignore: set_tcb_obj_ref set_sc_obj_ref
       wp: misc_cur_sc_chargeable_const crunch_wps maybeM_inv)

crunches reply_unlink_sc
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  (wp: crunch_wps)

lemma fkh_budget_conditions_kheap_update_consthh[wp]:
  "update_sk_obj_ref h update ref new \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding cur_sc_chargeable_def
  by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma reply_unlink_sc_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable \<rbrace>
   reply_unlink_sc sc r
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding reply_unlink_sc_def cur_sc_chargeable_def2
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' get_simple_ko_wp | wps)+
  by auto

lemma reply_remove_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   reply_remove t r
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding reply_remove_def sched_context_donate_def reply_unlink_tcb_def
  supply if_split [split del]
  apply (wpsimp wp: assert_inv)
            apply (wpsimp simp: set_thread_state_def set_thread_state_act_def
                            wp: set_object_wp)
           apply (wpsimp wp: update_sk_obj_ref_wp)
          apply (wpsimp wp: assert_inv )
         apply (wpsimp wp: gts_wp)
        apply (wpsimp wp: assert_inv )
       apply (wpsimp wp: get_simple_ko_wp)
      apply wpsimp
            apply (wpsimp wp: set_tcb_obj_ref_wp)
           apply (wpsimp wp: set_sc_obj_ref_wp)
          apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
                 in hoare_strengthen_post[rotated])
           apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def is_tcb
                                 bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                          split: if_splits, fastforce)
          apply (wpsimp simp: test_reschedule_def)
             apply (wpsimp wp: set_tcb_obj_ref_wp)
            apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
                   in hoare_strengthen_post[rotated])
             apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def is_tcb
                                   bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                            split: if_splits, fastforce)
            apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)
           apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp assert_opt_inv)
          apply (wpsimp wp: assert_opt_inv)
         apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)
        apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
               in hoare_strengthen_post[rotated])
         apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def is_tcb
                               bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                        split: if_splits)
        apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def is_tcb
                        bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                 split: if_splits)
  done

lemma set_thread_state_Inactive_csctb[wp]:
  "set_thread_state d Inactive \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def
                        bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                 dest!: get_tcb_SomeD
                 split: if_splits)
  by fastforce

lemma set_thread_state_csctb:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. (\<forall>x. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<longrightarrow> (x \<noteq> xa)))\<rbrace>
   set_thread_state xa d
   \<lbrace>\<lambda>xa. cur_sc_chargeable\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def
                        bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                 dest!: get_tcb_SomeD
                 split: if_splits)
  by fastforce


lemma restart_thread_if_no_fault_csctb:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. (\<forall>x. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<longrightarrow> (x \<noteq> xa)))\<rbrace>
   restart_thread_if_no_fault xa
   \<lbrace>\<lambda>xa. cur_sc_chargeable\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: possible_switch_to_def wp: hoare_drop_imp set_thread_state_csctb, fastforce)

lemma reply_unlink_tcb_csctb:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. (\<forall>x. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<longrightarrow> (x \<noteq> xa)))\<rbrace>
   reply_unlink_tcb xa r
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp wp: set_thread_state_csctb update_sk_obj_ref_wp gts_wp get_simple_ko_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def cur_sc_chargeable_def
                        bound_sc_tcb_at_kh_def st_tcb_at_kh_def obj_at_kh_def cur_tcb_def
                 dest!: get_tcb_SomeD
                 split: if_splits)
  by fastforce

lemma valid_ntfn_q_Blocked:
  "valid_ntfn_q (s:: det_state) \<Longrightarrow>
   (\<forall>p. case kheap s p of Some (Notification n) \<Rightarrow>
      \<forall>t \<in> set (ntfn_queue n). st_tcb_at (Not \<circ> not_blocked) t s
           | _ \<Rightarrow> True)"
  unfolding valid_ntfn_q_def2
  apply (clarsimp split: option.splits)
  apply (case_tac x2; clarsimp)
  apply (clarsimp simp: simple_obj_at_def)
  apply (drule_tac x=t and y=p in spec2, clarsimp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma restart_thread_if_no_fault_not_bound_sc_tcb_at[wp]:
  "restart_thread_if_no_fault x \<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P xs s\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by wpsimp

(* fixme: move *)
abbreviation
  "Blocked st \<equiv> (Not \<circ> not_blocked) st"

lemma cancel_all_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and valid_ep_q\<rbrace>
   cancel_all_ipc x
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_all_ipc_def
  apply wpsimp
      apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set queue. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s" in hoare_post_add)
      apply (rule mapM_x_wp[where S="set xs" and xs=xs for xs])
       apply wpsimp
           apply ((wpsimp wp: restart_thread_if_no_fault_csctb hoare_vcg_ball_lift restart_thread_if_no_fault_other reply_unlink_tcb_csctb
                              hoare_vcg_all_lift hoare_vcg_imp_lift'
                   | rule hoare_lift_Pf[where f = cur_sc])+)[3]
        apply (wp gts_wp)
       apply (clarsimp)
       apply (drule_tac x=x in bspec, simp)
       apply (intro conjI; clarsimp)
       apply clarsimp
      apply (wpsimp wp: set_simple_ko_wp get_ep_queue_wp)+
      apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set queue. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (x) s" in hoare_post_add)
      apply (rule mapM_x_wp[where S="set xs" and xs=xs for xs])
       apply wpsimp
           apply ((wpsimp wp: restart_thread_if_no_fault_csctb hoare_vcg_ball_lift restart_thread_if_no_fault_other reply_unlink_tcb_csctb
                              hoare_vcg_all_lift hoare_vcg_imp_lift'
                   | rule hoare_lift_Pf[where f = cur_sc])+)[3]
        apply (wp gts_wp)
       apply (clarsimp)
       apply (drule_tac x=x in bspec, simp)
       apply (intro conjI; clarsimp)
       apply clarsimp
      apply (wpsimp wp: set_simple_ko_wp get_ep_queue_wp get_simple_ko_wp)+
  apply (intro conjI; intro allI impI; intro conjI)
    apply (clarsimp)
    apply (subgoal_tac "st_tcb_at Blocked xaa s \<and> (xaa \<noteq> cur_thread s)")
        apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def
                              bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def
                       split: if_splits
               , fastforce)
      apply (clarsimp simp: valid_ep_q_def2 pred_neg_def pred_tcb_at_def obj_at_def simple_obj_at_def, fastforce)
    apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def st_tcb_at_kh_def
                          bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def
                   split: if_splits
           , fastforce)
    apply (clarsimp)
    apply (subgoal_tac "st_tcb_at Blocked xaa s \<and> (xaa \<noteq> cur_thread s)")
        apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def
                              bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def
                       split: if_splits
               , fastforce)
      apply (clarsimp simp: valid_ep_q_def2 pred_neg_def pred_tcb_at_def obj_at_def simple_obj_at_def, fastforce)
    apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def st_tcb_at_kh_def
                          bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def
                   split: if_splits
           , fastforce)
done

lemma possible_switch_to_cur_sc_chargeable[wp]:
  "possible_switch_to x \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding possible_switch_to_def
  by (wpsimp wp: hoare_drop_imp)

lemma cancel_all_signals_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and valid_ntfn_q\<rbrace>
   cancel_all_signals x
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding cancel_all_signals_def
  apply wpsimp
      apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set x2. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (x) s" in hoare_post_add)
      apply (rule mapM_x_wp[where S="set xs" and xs=xs for xs])
      apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_thread_state_csctb sts_st_tcb_at_other)
      apply (wps, wpsimp)
      apply (wps, wpsimp)
      apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_thread_state_csctb sts_st_tcb_at_other)
      apply (intro conjI; clarsimp)
      apply simp
     apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)+
  apply (intro conjI)
    apply clarsimp
    apply (subgoal_tac "st_tcb_at Blocked xaa s \<and> (xaa \<noteq> cur_thread s)")

    apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def
   bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def split: if_splits, fastforce)
      apply (clarsimp simp: valid_ntfn_q_def2 pred_neg_def pred_tcb_at_def obj_at_def simple_obj_at_def ntfn_queue_def
                     split: if_splits
             , fastforce)
    apply (clarsimp simp: obj_at_def cur_sc_chargeable_2_def pred_tcb_at_def
                          bound_sc_tcb_at_kh_def obj_at_kh_def ep_at_pred_def pred_neg_def st_tcb_at_kh_def
                   split: if_splits
           , fastforce)
  done

lemma blocked_cancel_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s) and st_tcb_at (not inactive) x\<rbrace>
   blocked_cancel_ipc a x c
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp wp: reply_unlink_tcb_csctb get_simple_ko_wp set_simple_ko_wp get_ep_queue_wp get_blocking_object_wp)
  apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                        cur_tcb_def is_tcb pred_neg_def)
  by fastforce

lemma reply_remove_tcb_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   reply_remove_tcb x b
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding reply_remove_tcb_def
  apply (wpsimp wp: reply_unlink_tcb_csctb update_sk_obj_ref_wp update_sched_context_wp get_sk_obj_ref_wp gts_wp)
  apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                    cur_tcb_def is_tcb pred_neg_def st_tcb_at_kh_def)
  by fastforce

lemma cancel_signal_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   cancel_signal x b
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_signal_def
  apply (wpsimp wp: reply_unlink_tcb_csctb set_simple_ko_wp get_simple_ko_wp)
  by (fastforce simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                      cur_tcb_def is_tcb pred_neg_def st_tcb_at_kh_def)

lemma thread_set_cur_sc_chargeable_indep:
  "\<forall>tcb. tcb_sched_context (a tcb) = tcb_sched_context (tcb) \<Longrightarrow>
   \<forall>tcb. tcb_state (a tcb) = tcb_state tcb \<Longrightarrow>
   thread_set a b \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                    cur_tcb_def is_tcb pred_neg_def st_tcb_at_kh_def ct_in_state_def
              dest!: get_tcb_SomeD)
  by fastforce

lemma cancel_ipc_cur_sc_chargeable2:
  "\<lbrace>cur_sc_chargeable and ct_not_blocked\<rbrace>
   cancel_ipc x
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_ipc_def
  apply (wpsimp wp: blocked_cancel_ipc_cur_sc_chargeable reply_remove_tcb_cur_sc_chargeable
                    cancel_signal_cur_sc_chargeable)
  apply (wpsimp wp: thread_set_cur_sc_chargeable_indep hoare_vcg_imp_lift' gts_wp thread_set_no_change_tcb_state)+
  apply (case_tac "x = cur_thread s")
  apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                    cur_tcb_def is_tcb pred_neg_def st_tcb_at_kh_def ct_in_state_def
              dest!: get_tcb_SomeD)
  apply (fastforce)
  apply (clarsimp simp: pred_neg_def pred_tcb_at_def obj_at_def)
  apply (fastforce)
  done

lemma cancel_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and cur_tcb and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   cancel_ipc x
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_ipc_def
  apply (wpsimp wp: blocked_cancel_ipc_cur_sc_chargeable
                    reply_remove_tcb_cur_sc_chargeable
                    cancel_signal_cur_sc_chargeable thread_set_wp gts_wp)
  by (fastforce simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                      cur_tcb_def is_tcb pred_neg_def st_tcb_at_kh_def
               dest!: get_tcb_SomeD)

lemma fast_finalise_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and valid_ep_q and valid_ntfn_q and invs
     and ct_not_blocked \<rbrace>
   fast_finalise d e
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac d; simp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_cur_sc_chargeable)
    apply (wpsimp wp: cancel_all_signals_cur_sc_chargeable)
   subgoal for x5
   apply (wpsimp wp: cancel_ipc_cur_sc_chargeable2 reply_remove_cur_sc_chargeable)
     apply (wpsimp wp: gts_wp get_simple_ko_wp)+
   apply (subgoal_tac "st_tcb_at (not not_blocked) x s")
    apply (fastforce simp: ct_in_state_def pred_tcb_at_def pred_neg_def obj_at_def)
   apply (subgoal_tac "(x5, TCBReply) \<in> state_refs_of s x")
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                          pred_neg_def
                   split: thread_state.splits if_splits)
   apply (erule reply_tcb_not_idle_thread_helper, simp add: obj_at_def, clarsimp)
   done
  apply (wpsimp wp: set_sc_obj_ref_cur_sc_chargeable_const)
  done

lemma set_cap_cur_sc_chargeablep[wp]:
  "\<lbrace>cur_sc_chargeable\<rbrace>
   set_cap d a
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
   unfolding set_cap_def
   apply (wpsimp wp: set_object_wp get_object_wp)
   by (fastforce simp: cur_sc_chargeable_def bound_sc_tcb_at_kh_def obj_at_kh_def
                         obj_at_def st_tcb_at_kh_def)

lemma set_cdt_cur_sc_chargeablep[wp]:
  "\<lbrace>cur_sc_chargeable\<rbrace>
   set_cdt d
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
   unfolding set_cdt_def
   by (wpsimp wp: set_object_wp get_object_wp)

crunches empty_slot
  for cur_sc_chargeable[wp]: "cur_sc_chargeable :: det_state \<Rightarrow> _"
  (ignore: set_tcb_obj_ref set_sc_obj_ref
       wp: misc_cur_sc_chargeable_const crunch_wps simp: crunch_simps)

lemma cap_delete_one_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked and valid_ep_q and valid_ntfn_q\<rbrace>
   cap_delete_one d
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: get_cap_wp fast_finalise_cur_sc_chargeable)

crunches deleting_irq_handler
  for cur_sc_chargeable[wp]: "cur_sc_chargeable :: det_state \<Rightarrow> _"
  (ignore: set_tcb_obj_ref set_sc_obj_ref
       wp: misc_cur_sc_chargeable_const crunch_wps simp: crunch_simps)

lemma suspend_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and ct_not_blocked\<rbrace>
   suspend x
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding suspend_def
  apply (wpsimp wp: set_tcb_obj_ref_cur_sc_chargeable_const
                    set_sc_obj_ref_cur_sc_chargeable_const hoare_drop_imp
                    cancel_ipc_cur_sc_chargeable2)
  done

(* FIXME: set_tcb_obj_ref does more than set tcb object references *)

lemma set_tcb_obj_ref_ct_in_state:
  "\<forall>tcb. tcb_state (f (\<lambda>_. C) tcb) = tcb_state tcb \<Longrightarrow>
   set_tcb_obj_ref f ptr C \<lbrace>ct_in_state P\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
              dest!: get_tcb_SomeD)

crunches unbind_from_sc, unbind_notification
  for ct_in_state[wp]: "ct_in_state P"
  (wp: crunch_wps hoare_drop_imp hoare_vcg_all_lift)

lemma finalise_cap_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked and valid_ep_q and valid_ntfn_q\<rbrace>
   finalise_cap d f
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (case_tac d; simp)
               apply wpsimp
              apply wpsimp
             apply (wpsimp wp: cancel_all_ipc_cur_sc_chargeable)
             apply (clarsimp split: if_split)
            apply (wpsimp wp: cancel_all_signals_cur_sc_chargeable)
            apply (clarsimp split: if_split)
           apply (wpsimp wp: cancel_ipc_cur_sc_chargeable reply_remove_cur_sc_chargeable
                             gts_wp get_simple_ko_wp)
           apply (clarsimp split: if_split)
           apply (subgoal_tac "st_tcb_at (not not_blocked) x s")
            apply (fastforce simp: ct_in_state_def pred_tcb_at_def pred_neg_def obj_at_def)
           apply (subgoal_tac "(x5, TCBReply) \<in> state_refs_of s x")
            apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                                  pred_neg_def
                           split: thread_state.splits if_splits)
           apply (erule reply_tcb_not_idle_thread_helper, simp add: obj_at_def, clarsimp)
          apply wpsimp
         apply (wpsimp wp: suspend_cur_sc_chargeable)
         apply (clarsimp split: if_split)
        apply wpsimp
       apply (wpsimp wp: set_sc_obj_ref_cur_sc_chargeable_const)
      apply wpsimp+
  done

crunches complete_yield_to, sched_context_unbind_tcb
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma unbind_from_sc_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace> unbind_from_sc param_a \<lbrace>\<lambda>_. ct_not_in_release_q:: det_state \<Rightarrow> _\<rbrace>"
  unfolding unbind_from_sc_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp)
  done

crunches finalise_cap
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunches cap_swap_for_delete
  for valid_ep_q[wp]: "valid_ep_q:: det_state \<Rightarrow> _"
  and valid_ntfn_q[wp]: "valid_ntfn_q :: det_state \<Rightarrow> _"

crunches empty_slot
  for valid_ep_q[wp]: "valid_ep_q:: det_state \<Rightarrow> _"
  and valid_ntfn_q[wp]: "valid_ntfn_q :: det_state \<Rightarrow> _"

lemma set_x_obj_ref_ep_at_pred[wp]:
  "set_tcb_obj_ref f x v \<lbrace>\<lambda>s. Q (ep_at_pred P p s)\<rbrace>"
  "set_sc_obj_ref a b c \<lbrace>\<lambda>s. Q (ep_at_pred P p s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp, erule back_subst[where P=Q], clarsimp simp: simple_obj_at_def obj_at_def)
  apply (wpsimp wp: set_sc_obj_ref_wp, erule back_subst[where P=Q], clarsimp simp: simple_obj_at_def obj_at_def)
  done

lemma set_tcb_pred_tcb_const:
  "(\<And>tcb. P (proj (tcb_to_itcb (f (\<lambda>y. v) tcb))) = P (proj (tcb_to_itcb tcb))) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>\<lambda>s. Q (pred_tcb_at proj P p s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma set_tcb_active_sc_tcb_at_const:
  "(\<And>tcb. (tcb_sched_context ( (f (\<lambda>y. v) tcb))) = (tcb_sched_context ( tcb)) ) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>active_sc_tcb_at t\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (clarsimp simp: active_sc_tcb_at_def obj_at_def pred_tcb_at_def test_sc_refill_max_def
                 split: option.splits, fastforce)
  done

lemma set_tcb_budget_ready_const:
  "(\<And>tcb. (tcb_sched_context ( (f (\<lambda>y. v) tcb))) = (tcb_sched_context ( tcb)) ) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>budget_ready t\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (clarsimp simp: budget_ready_defs obj_at_def pred_tcb_at_def
                 split: option.splits)
  apply auto
  apply (rule_tac x=scp in exI, simp)
  apply fastforce
  apply (rule_tac x=scp in exI, simp)
  apply fastforce
  done

lemma set_tcb_budget_sufficient_const:
  "(\<And>tcb. (tcb_sched_context ( (f (\<lambda>y. v) tcb))) = (tcb_sched_context ( tcb)) ) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>budget_sufficient t\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (clarsimp simp: budget_sufficient_defs obj_at_def pred_tcb_at_def
                 split: option.splits)
  apply auto
  apply (rule_tac x=scp in exI, simp)
  apply fastforce
  apply (rule_tac x=scp in exI, simp)
  apply fastforce
  done

lemmas set_tcb_obj_ref_budget_ready_indep = set_tcb_pred_tcb_const
                                            set_tcb_budget_sufficient_const
                                            set_tcb_active_sc_tcb_at_const
                                            set_tcb_budget_ready_const

lemma set_tcb_obj_ref_valid_ep_q_const:
  "(\<And>tcb.  (tcb_state ( tcb)) =  (tcb_state ( (f (\<lambda>y. v) tcb)))) \<Longrightarrow>
   (\<And>tcb.  (tcb_sched_context ( tcb)) =  (tcb_sched_context ( (f (\<lambda>y. v) tcb)))) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>valid_ep_q\<rbrace>"
  apply (wpsimp simp: valid_ep_q_def2)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_tcb_pred_tcb_const hoare_vcg_disj_lift
                    set_tcb_obj_ref_budget_ready_indep)
  done

lemma set_sc_obj_ref_valid_ep_q_const:
  "(\<And>sc. sc_refill_max (f (\<lambda>a. v) sc) = sc_refill_max sc) \<Longrightarrow>
   (\<And>sc. sc_refills (f (\<lambda>a. v) sc) = sc_refills sc) \<Longrightarrow>
   set_sc_obj_ref f x v \<lbrace>valid_ep_q:: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_ep_q_def2)
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift set_sc_active_sc_tcb_at_const set_sc_budget_sufficient_const
                    set_sc_obj_ref_budget_ready_const)

(* FIXME: move *)
lemma update_sko_sko_at_pred_indep_types:
  "(\<forall>x y. D x \<noteq> C y) \<Longrightarrow> inj D \<Longrightarrow>
   update_sk_obj_ref D f ref new \<lbrace>\<lambda>s. Q (sk_obj_at_pred C proj P p s)\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: obj_at_def sk_obj_at_pred_def)
  done

lemma test_sc_refill_max_equiv:
  "test_sc_refill_max scp s = sc_at_pred sc_refill_max (\<lambda>x. 0 < x) scp s"
  unfolding test_sc_refill_max_def
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def split: option.splits)
  apply (case_tac x2; simp)
  done

lemma set_simple_obj_ref_refill_conditions[wp]:
  "set_ntfn_obj_ref f x v \<lbrace>is_refill_sufficient scp k\<rbrace>"
  "set_ntfn_obj_ref f x v \<lbrace>is_refill_ready scp k\<rbrace>"
  "set_reply_obj_ref g x v \<lbrace>is_refill_sufficient scp k\<rbrace>"
  "set_reply_obj_ref g x v \<lbrace>is_refill_ready scp k\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: is_refill_sufficient_def obj_at_def)
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: is_refill_ready_def obj_at_def)
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: is_refill_sufficient_def obj_at_def)
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: is_refill_ready_def obj_at_def)
  done

lemma set_reply_obj_ref_sc_at_pred_n[wp]:
  "set_reply_obj_ref update ref new \<lbrace>\<lambda>s. P (sc_at_pred_n f g h sc s)\<rbrace>"
  by (wpsimp wp: update_sk_obj_ref_wp simp: sc_at_pred_n_def obj_at_def)

lemma set_ntfn_obj_ref_valid_ep_q:
  "set_ntfn_obj_ref f x v \<lbrace>valid_ep_q\<rbrace>"
  apply (wpsimp simp: valid_ep_q_def2)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_tcb_pred_tcb_const hoare_vcg_disj_lift
                    set_tcb_obj_ref_budget_ready_indep update_sko_sko_at_pred_indep_types)
  apply (clarsimp simp: bound_sc_budget_conditions_equiv test_sc_refill_max_equiv)
  apply (wpsimp wp: hoare_vcg_ex_lift)
  apply (clarsimp simp: bound_sc_budget_conditions_equiv test_sc_refill_max_equiv)
  done

lemma set_reply_obj_ref_valid_ep_q:
  "set_reply_obj_ref f x v \<lbrace>valid_ep_q\<rbrace>"
  apply (wpsimp simp: valid_ep_q_def2)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_tcb_pred_tcb_const hoare_vcg_disj_lift
                    set_tcb_obj_ref_budget_ready_indep update_sko_sko_at_pred_indep_types)
  apply (clarsimp simp: bound_sc_budget_conditions_equiv test_sc_refill_max_equiv)
  apply (wpsimp wp: hoare_vcg_ex_lift)
  apply (clarsimp simp: bound_sc_budget_conditions_equiv test_sc_refill_max_equiv)
  done

crunches tcb_release_remove, tcb_sched_action
  for valid_ep_q[wp]: valid_ep_q

lemma sched_context_maybe_unbind_ntfn_valid_ep_q[wp]:
  "sched_context_maybe_unbind_ntfn x41 \<lbrace>valid_ep_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_maybe_unbind_ntfn_def
  by (wpsimp wp: set_sc_obj_ref_valid_ep_q_const set_ntfn_obj_ref_valid_ep_q hoare_drop_imp)

lemma set_thread_state_valid_ep_q_not_in_ep_q:
  "\<lbrace> valid_ep_q and not in_ep_q thread\<rbrace> set_thread_state thread ts \<lbrace> \<lambda>_. valid_ep_q \<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ep_q_def pred_neg_def dest!: get_tcb_SomeD split: option.splits)
  apply (drule_tac x=p in spec)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (drule_tac x=t in bspec, simp)
  apply (rule conjI, clarsimp simp: st_tcb_at_kh_if_split in_ep_q_def simple_obj_at_def)
  apply (elim conjE disjE)
   apply (clarsimp simp: bound_sc_tcb_at_kh_if_split  in_ep_q_def simple_obj_at_def)
  apply (rule disjI2)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs)
  apply (rename_tac scp sc n)
  apply (intro conjI, clarsimp simp: bound_sc_tcb_at_kh_if_split  in_ep_q_def simple_obj_at_def)
  apply clarsimp
  by (intro conjI; rule_tac x=scp in exI; fastforce)

lemma in_ep_q_lift:
  assumes A: "\<And>P R p. f \<lbrace>(\<lambda>s. (ep_at_pred R p s)) :: det_state \<Rightarrow> _\<rbrace>"
  shows "f \<lbrace>(\<lambda>s. (in_ep_q t s)) :: det_state \<Rightarrow> _\<rbrace>"
  unfolding  in_ep_q_def
  by (wpsimp wp: A hoare_vcg_ex_lift)

lemma not_in_ep_q_lift:
  assumes A: "\<And>P R p. f \<lbrace>(\<lambda>s. \<not> (ep_at_pred R p s)) :: det_state \<Rightarrow> _\<rbrace>"
  shows "f \<lbrace>(\<lambda>s. (\<not> in_ep_q t s)) :: det_state \<Rightarrow> _\<rbrace>"
  unfolding  in_ep_q_def
  by (wpsimp wp: A hoare_vcg_all_lift)

lemma unbind_notification_valid_ep_q[wp]:
  "unbind_notification x7  \<lbrace>valid_ep_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding unbind_notification_def
  by (wpsimp wp: set_tcb_obj_ref_valid_ep_q_const set_ntfn_obj_ref_valid_ep_q  hoare_drop_imp)

lemma finalise_cap_valid_ipc_q:
  "finalise_cap cap fin \<lbrace> valid_ep_q:: det_state \<Rightarrow> _\<rbrace>"
  "finalise_cap cap fin \<lbrace> valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  sorry (* valid_ipc_qs: finalise_cap *)

lemma cap_delete_valid_ipc_q:
  "cap_delete x \<lbrace>valid_ep_q:: det_state \<Rightarrow> _\<rbrace>"
  "cap_delete x \<lbrace>valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_def
  apply (wpsimp wp: rec_del_preservation finalise_cap_valid_ipc_q preemption_point_inv)
  apply (wpsimp wp: rec_del_preservation finalise_cap_valid_ipc_q preemption_point_inv)
  done

lemma install_tcb_cap_valid_ipc_q:
  "install_tcb_cap x41 c d e \<lbrace>valid_ep_q:: det_state \<Rightarrow> _\<rbrace>"
  "install_tcb_cap x41 c d e \<lbrace>valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  apply (wpsimp wp: check_cap_inv cap_delete_valid_ipc_q)
  apply (wpsimp wp: check_cap_inv cap_delete_valid_ipc_q)
  done

lemma rec_del_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace> rec_del call \<lbrace>\<lambda>rv. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  by (rule_tac Q="\<lambda>_. scheduler_act_sane and valid_ep_q and valid_ntfn_q" in hoare_strengthen_post[rotated],
      simp,
      wpsimp wp: rec_del_preservation preemption_point_inv finalise_cap_valid_ipc_q)

crunches cap_delete
  for simple_sched_action[wp]: simple_sched_action

crunches cap_swap_for_delete, empty_slot
  for ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
  and ct_not_in_release_q[wp]: "ct_not_in_release_q :: det_state \<Rightarrow> _"
  and cur_sc_chargeable[wp]: "cur_sc_chargeable :: det_state \<Rightarrow> _"

lemma rec_del_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post, rule rec_del_preservation)
  by (wpsimp wp:  preemption_point_inv' finalise_cap_valid_ipc_q)+

lemma rec_del_ct_not_in_release_q[wp]:
  "rec_del call \<lbrace>ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: rec_del_preservation preemption_point_inv')

end

crunches tcb_sched_action
for ct_in_state[wp]: "ct_in_state P"
and not_pred_tcb[wp]: "\<lambda>s. \<not> pred_tcb_at proj P t s"

lemma ct_in_state_def2: "ct_in_state test s = st_tcb_at test (cur_thread s) s"
   by (simp add: ct_in_state_def)

crunches reorder_ntfn, reorder_ep
  for valid_sched[wp]:"valid_sched::det_state \<Rightarrow> _"
  and simple_sched_action[wp]: simple_sched_action
  (wp: mapM_wp' get_simple_ko_wp)

lemma thread_set_priority_not_st_tcb_at[wp]:
  "\<lbrace>\<lambda>s. \<not> st_tcb_at P t s\<rbrace> thread_set_priority p t' \<lbrace>\<lambda>rv s. \<not> st_tcb_at P t s\<rbrace>"
  unfolding thread_set_priority_def
  by (wpsimp wp: thread_set_no_change_tcb_state_converse)

lemma thread_set_priority_test_sc_refill_max[wp]:
  "\<lbrace>\<lambda>s. test_sc_refill_max t s\<rbrace> thread_set_priority p t' \<lbrace>\<lambda>rv s. test_sc_refill_max t s\<rbrace>"
  unfolding thread_set_priority_def
  by (wpsimp simp: thread_set_def set_object_def;
      clarsimp dest!: get_tcb_SomeD simp: test_sc_refill_max_def)

lemma thread_set_priority_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace> thread_set_priority p t' \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  unfolding thread_set_priority_def
  apply (wpsimp simp: thread_set_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
  by (intro conjI impI; fastforce simp: test_sc_refill_max_def)

lemma thread_set_priority_valid_ready_qs_not_q:
  "\<lbrace>valid_ready_qs and not_queued t\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ready_qs_def etcb_defs not_queued_def dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp)
  apply (clarsimp simp: st_tcb_at_kh_def st_tcb_at_def active_sc_tcb_at_defs
                        refill_sufficient_kh_def refill_ready_kh_def
                        is_refill_sufficient_def is_refill_ready_def)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=ta in bspec, simp, clarsimp)
  apply (rename_tac scp sc n)
  apply (intro conjI; rule_tac x=scp in exI; fastforce)
  done

lemma thread_set_priority_budget_ready[wp]:
  "\<lbrace>\<lambda>s. budget_ready t s\<rbrace> thread_set_priority t' p \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  unfolding thread_set_priority_def
  apply (wpsimp simp: thread_set_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: is_refill_ready_def pred_tcb_at_def obj_at_def)
  by (intro conjI impI; rule_tac x=scp in exI; clarsimp)

lemma thread_set_priority_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. budget_sufficient t s\<rbrace> thread_set_priority t' p \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  unfolding thread_set_priority_def
  apply (wpsimp simp: thread_set_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: is_refill_sufficient_def pred_tcb_at_def obj_at_def)
  by (intro conjI impI; rule_tac x=scp in exI; clarsimp)

lemma thread_set_priority_valid_release_q_not_q:
  "\<lbrace>valid_release_q\<rbrace> thread_set_priority t' p \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp wp: set_object_wp) solve_valid_release_q

lemma thread_set_priority_ct_not_in_q[wp]:
  "thread_set_priority p t \<lbrace>ct_not_in_q\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp wp: set_object_wp)

lemma thread_set_priority_valid_sched_action[wp]:
  "thread_set_priority p t \<lbrace>valid_sched_action\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_2_def
                        active_sc_tcb_at_defs switch_in_cur_domain_def in_cur_domain_def
                        is_activatable_def st_tcb_at_kh_def etcb_at'_def  etcbs_of'_def
                        refill_prop_defs
                split: option.splits
                 dest!: get_tcb_SomeD)
  by (intro impI allI conjI; fastforce)+

lemma thread_set_priority_ct_in_cur_domain[wp]:
  "thread_set_priority p t \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_2_def etcb_at'_def etcbs_of'_def
                 dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_valid_idle_etcb[wp]:
  "thread_set_priority t p \<lbrace>valid_idle_etcb\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp wp_del: valid_idle_etcb_lift)
  apply (clarsimp simp: valid_idle_etcb_def etcbs_of'_def etcb_at'_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_not_cur_thread[wp]:
  "thread_set_priority p t \<lbrace>not_cur_thread t'\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp wp: set_object_wp)

lemma thread_set_priority_valid_blocked_except[wp]:
  "thread_set_priority p t \<lbrace>valid_blocked_except_set S\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: valid_blocked_except_def st_tcb_at_kh_def active_sc_tcb_at_defs
                   split: option.splits dest!:get_tcb_SomeD)

lemma thread_set_priority_weak_valid_sched_action[wp]:
  "thread_set_priority t p \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
                 dest!: get_tcb_SomeD
                 split: option.splits)
  by (intro impI allI conjI; fastforce)+

lemma thread_set_priority_switch_in_cur_domain[wp]:
  "thread_set_priority t p \<lbrace>switch_in_cur_domain\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at'_def etcbs_of'_def
                 dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_activatable[wp]:
  "thread_set_priority t p \<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_valid_sched[wp]:
  "\<lbrace>valid_sched and not_queued t\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  by (wpsimp wp: thread_set_priority_valid_ready_qs_not_q thread_set_priority_valid_release_q_not_q)

lemma thread_set_priority_is_schedulable_opt[wp]:
  "\<lbrace>\<lambda>s.  P (is_schedulable_opt tptr inq s) \<rbrace>
     thread_set_priority t p \<lbrace>\<lambda>_ s. P (is_schedulable_opt tptr inq s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  by (clarsimp simp: is_schedulable_opt_def get_tcb_def test_sc_refill_max_def
                split: option.splits)

lemma thread_set_priority_in_release_queue[wp]:
  "\<lbrace>\<lambda>s.  P (in_release_queue t s) \<rbrace>
     thread_set_priority t p \<lbrace>\<lambda>_ s. P (in_release_queue t s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  by (clarsimp simp: in_release_queue_def get_tcb_def
                split: option.splits)

lemma thread_set_priority_is_schedulable_opt_queue[wp]:
  "\<lbrace>\<lambda>s.  P (is_schedulable_opt tptr (in_release_queue tptr s) s) \<rbrace>
     thread_set_priority t p \<lbrace>\<lambda>_ s. P (is_schedulable_opt tptr (in_release_queue tptr s) s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  by (clarsimp simp: is_schedulable_opt_def get_tcb_def test_sc_refill_max_def in_release_queue_def
                split: option.splits)

lemma is_schedulable_opt_ready_queues_update[simp]:
  "is_schedulable_opt t q (ready_queues_update f s) = is_schedulable_opt t q s"
  by (clarsimp simp: is_schedulable_opt_def get_tcb_def test_sc_refill_max_def
                  split: option.splits)

(* FIXME: move *)
lemma tcb_sched_dequeue_valid_sched_in_release_queue:
  "\<lbrace>valid_sched and in_release_queue thread and ready_or_released\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state\<Rightarrow>_\<rbrace>"
  apply (wpsimp wp: tcb_sched_dequeue_valid_sched_not_queued)
  by (simp add: ready_or_released_in_release_queue)

lemma ct_not_in_q_not_cur_threadE:
  "tptr \<in> set (ready_queues s d p)
   \<Longrightarrow> ct_not_in_q s
   \<Longrightarrow> not_cur_thread tptr s"
  by (clarsimp simp: ct_not_in_q_def not_cur_thread_def not_queued_def)

lemma reschedule_required_valid_sched:
  "\<lbrace>valid_sched\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def wp: reschedule_required_valid_blocked)

lemma set_priority_valid_sched:
  "\<lbrace>valid_sched and ct_ARS and ct_active\<rbrace>
   set_priority tptr prio
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_priority_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_vcg_if_lift2 reschedule_required_valid_sched'
                    tcb_sched_enqueue_valid_blocked_enqueue)
          apply (wpsimp wp: thread_set_priority_valid_ready_qs_not_q
                            thread_set_priority_valid_release_q_not_q)
         apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                           tcb_sched_dequeue_valid_blocked_except_set_const)
        apply (wpsimp wp: thread_set_priority_valid_sched)
       apply wpsimp+
    apply (rule_tac Q="\<lambda>r. valid_sched" in hoare_strengthen_post; wpsimp)
   apply (rule_tac Q="\<lambda>r. valid_sched" in hoare_strengthen_post; wpsimp)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def)
  apply (intro conjI; intro impI allI)
   apply (intro conjI; intro impI allI)
     apply (clarsimp simp: valid_ready_qs_def)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (fastforce simp: not_queued_def valid_ready_qs_def obj_at_def pred_tcb_at_def etcb_defs)
  apply (fastforce simp: not_queued_def valid_ready_qs_def obj_at_def pred_tcb_at_def)
  done

lemma set_mcpriority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mcpriority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

crunch simple_sched_action[wp]: set_mcpriority,thread_set_priority simple_sched_action
  (wp: maybeM_inv)

lemma set_priority_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_priority param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  unfolding set_priority_def
  by(wpsimp simp: get_thread_state_def thread_get_def wp: maybeM_inv)

lemma set_tcb_sched_context_valid_sched_except_blocked_None:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except tptr and (\<lambda>s. tptr \<noteq> idle_thread s)
    and not_queued tptr and not_in_release_q tptr and simple_sched_action\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update tptr None
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_sched_def dest!: get_tcb_SomeD)
  apply (intro conjI)
       apply (clarsimp simp: valid_ready_qs_def etcb_defs not_queued_def
                             active_sc_tcb_at_defs st_tcb_at_kh_if_split refill_prop_defs
                      split: option.splits)
       apply (drule_tac x=d and y=p in spec2, clarsimp)
       apply (drule_tac x=t in bspec, simp, fastforce)
      apply (solve_valid_release_q csimp: not_in_release_q_def)
     apply (fastforce simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def
                            get_tcb_rev simple_sched_action_def st_tcb_at_kh_if_split
                            active_sc_tcb_at_defs etcb_defs switch_in_cur_domain_def
                     split: option.splits)
    apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcb_defs get_tcb_rev)
   apply (clarsimp simp: valid_blocked_def valid_blocked_except_def st_tcb_at_kh_if_split
                         active_sc_tcb_at_defs get_tcb_rev
                  split: option.splits if_splits)
   apply (drule_tac x=t in spec)
   apply (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
                  split: option.splits)
  apply (clarsimp simp: valid_idle_etcb_def etcb_defs get_tcb_rev split: option.splits)
  done

lemma postpone_in_release_q:
  "\<lbrace>sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>r. in_release_q tcbptr\<rbrace>"
  apply (clarsimp simp: postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (clarsimp split: option.splits)
  apply (case_tac "x2 = tcbptr")
   apply (wpsimp wp: tcb_release_enqueue_in_release_q)
  apply (rule_tac Q="\<lambda>s. False" in hoare_weaken_pre, simp)
  apply (clarsimp simp: pred_conj_def sc_tcb_sc_at_def obj_at_def)
  apply (drule_tac s="Some tcbptr" in sym, simp)
  done

lemma sched_context_resume_cond_has_budget:
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr
    and sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr
    and st_tcb_at runnable tcbptr\<rbrace>
   sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>rv s. active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> has_budget tcbptr s\<rbrace>"
  unfolding sched_context_resume_def
  apply wpsimp
               apply (rule_tac Q="\<lambda>r. DetSchedInvs_AI.in_release_q tcbptr" in hoare_strengthen_post)
                prefer 2
                apply (clarsimp simp: pred_neg_def not_in_release_q_def in_release_q_def)
               apply (wpsimp wp: postpone_in_release_q)+
       apply (wpsimp simp: thread_get_def
                       wp: is_schedulable_wp refill_sufficient_wp refill_ready_wp)+
  apply safe
     apply (clarsimp simp: has_budget_equiv2 st_tcb_at_def obj_at_def
                    dest!: is_schedulable_opt_Some get_tcb_SomeD)
    apply (clarsimp simp: has_budget_equiv2 st_tcb_at_def obj_at_def pred_tcb_at_def active_sc_tcb_at_def
                          test_sc_refill_max_def
                   dest!: is_schedulable_opt_Some get_tcb_SomeD)
   apply (simp only: has_budget_equiv2 pred_tcb_at_eq_commute)
   apply (intro disjI2 conjI)
     apply simp
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def sufficient_refills_defs
                   dest!: get_tcb_SomeD)
   apply (clarsimp simp: is_refill_ready_def pred_tcb_at_def obj_at_def
                  dest!: get_tcb_SomeD)
  apply (clarsimp simp: has_budget_equiv2 sc_at_pred_n_def obj_at_def
                 dest!: is_schedulable_opt_Some get_tcb_SomeD)
  apply (clarsimp simp: not_in_release_q_def in_release_queue_def)
  done

lemma sched_context_resume_cond_budget_ready_sufficient:
  "\<lbrace>bound_sc_tcb_at (\<lambda>a. a = sc_opt) tcbptr
    and (\<lambda>s. \<forall>sc_ptr. sc_opt = (Some sc_ptr)
                      \<longrightarrow> (sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr s))\<rbrace>
    sched_context_resume sc_opt
   \<lbrace>\<lambda>rv s. st_tcb_at runnable tcbptr s \<and> active_sc_tcb_at tcbptr s \<and> not_in_release_q tcbptr s \<longrightarrow>
           budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_resume_def
  apply wpsimp
               apply (rule_tac Q="\<lambda>r. in_release_queue tcbptr" in hoare_strengthen_post)
                prefer 2
                apply (clarsimp simp: in_release_queue_def not_in_release_q_def)
               apply (wpsimp simp: in_release_queue_in_release_q
                               wp: postpone_in_release_q refill_sufficient_wp refill_ready_wp)+
       apply (wpsimp simp: thread_get_def wp: is_schedulable_wp)+
  apply (intro conjI; intro impI allI)
   apply (intro conjI; intro impI allI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def
                   dest!: is_schedulable_opt_Some get_tcb_SomeD)
    apply (clarsimp simp: sc_at_pred_n_def is_refill_ready_def sufficient_refills_defs
                          is_refill_sufficient_def active_sc_tcb_at_defs)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def
                  dest!: is_schedulable_opt_Some get_tcb_SomeD)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def  pred_tcb_at_def
                          active_sc_tcb_at_def )
   apply (clarsimp simp: in_release_queue_def not_in_release_q_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
  done

lemma tcb_sched_context_update_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread tcbptr\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update tcbptr' scptr_opt
   \<lbrace>\<lambda>rv s. not_cur_thread tcbptr s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def)

lemma sc_tcb_update_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread tcbptr\<rbrace>
     set_sc_obj_ref sc_tcb_update scptr tptr_opt
   \<lbrace>\<lambda>rv s. not_cur_thread tcbptr s\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def
               wp: get_object_wp)

lemma sc_tcb_update_Some_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and bound_sc_tcb_at ((=) None) tptr\<rbrace>
     set_sc_obj_ref sc_tcb_update scptr (Some tptr)
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp simp: set_sc_obj_ref_def)
  apply (clarsimp simp: valid_ready_qs_def)
  apply (safe)
      apply (clarsimp simp: etcb_at'_def etcbs_of'_def)
     apply (fastforce simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def
                            obj_at_def)
    apply (fastforce simp: active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_def obj_at_kh_def
                           active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_kh_def
                           test_sc_refill_max_def)
   apply (fastforce simp: pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                          refill_sufficient_kh_def is_refill_sufficient_def)
  apply (fastforce simp: pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
                         refill_ready_kh_def is_refill_ready_def)
  done

lemma sc_tcb_update_Some_valid_release_q[wp]:
  "\<lbrace>valid_release_q and bound_sc_tcb_at ((=) None) tptr\<rbrace>
     set_sc_obj_ref sc_tcb_update scptr (Some tptr)
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wpsimp wp: update_sched_context_wp simp: set_sc_obj_ref_def)
     (solve_valid_release_q fsimp: st_tcb_at_kh_def)

lemma sc_tcb_update_Some_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain and bound_sc_tcb_at ((=) None) tptr\<rbrace>
     set_sc_obj_ref sc_tcb_update scptr (Some tptr)
   \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp simp: set_sc_obj_ref_def)
  apply (clarsimp simp: ct_in_cur_domain_def)
  apply (clarsimp simp: in_cur_domain_def etcb_at_def etcbs_of'_def)
  apply (case_tac "cur_thread s = scptr"; simp)
  done

lemma sc_tcb_update_sc_tcb_sc_at:
  "\<lbrace>K (P t)\<rbrace> set_sc_obj_ref sc_tcb_update sc t \<lbrace>\<lambda>rv. sc_tcb_sc_at P sc\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_wp)
  by (clarsimp simp: obj_at_def sc_at_pred_n_def)

lemma sched_context_bind_tcb_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and bound_sc_tcb_at ((=) None) tcbptr and
    (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)\<rbrace>
   sched_context_bind_tcb scptr tcbptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_bind_tcb_def
  apply clarsimp
  apply (wpsimp wp: is_schedulable_wp reschedule_valid_sched_const)
     apply (rule_tac Q="\<lambda>r s. valid_sched_except_blocked s
                              \<and> valid_blocked_except_set {tcbptr} s
                              \<and> not_cur_thread tcbptr s
                              \<and> (st_tcb_at runnable tcbptr s \<and> active_sc_tcb_at tcbptr s \<and>
                                 not_in_release_q tcbptr s \<longrightarrow>
                                 budget_ready tcbptr s \<and> budget_sufficient tcbptr s)"
                     in hoare_strengthen_post[rotated])
     apply (intro allI conjI;
            intro impI;
            clarsimp simp: valid_sched_def dest!: is_schedulable_opt_Some)
      apply (fastforce elim!: valid_blocked_divided2
                        simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def)
     apply (wpsimp wp: sched_context_resume_valid_sched_except_blocked
                       sched_context_resume_valid_blocked_except_set
                       sched_context_resume_cond_budget_ready_sufficient)
    apply (rule_tac Q="\<lambda>r. valid_sched_except_blocked and
                           valid_blocked_except_set {tcbptr} and
                           scheduler_act_not tcbptr and
                           not_queued tcbptr and
                           not_cur_thread tcbptr and
                           sc_tcb_sc_at ((=) (Some tcbptr)) scptr and
                           bound_sc_tcb_at (\<lambda>a. a = Some scptr) tcbptr"
                    in hoare_strengthen_post[rotated])
     apply (clarsimp simp: sc_at_pred_n_eq_commute )
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def)
    apply (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                      set_tcb_sched_context_valid_release_q_not_queued
                      set_tcb_sched_context_simple_valid_sched_action
                      set_tcb_sched_context_Some_valid_blocked_except
                      ssc_bound_sc_tcb_at)
   apply (clarsimp simp:  )
   apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_disj_lift sc_tcb_update_sc_tcb_sc_at)
  apply (clarsimp simp: valid_sched_def cong: conj_cong)
  apply (safe)
    apply (fastforce simp: valid_ready_qs_def not_queued_def pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: valid_release_q_def not_in_release_q_def pred_tcb_at_def obj_at_def
                         active_sc_tcb_at_def)
   apply fastforce
  apply (clarsimp simp: not_cur_thread_def pred_tcb_at_def obj_at_def)
  done

lemma maybe_sched_context_bind_tcb_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and bound_sc_tcb_at ((=) None) tcbptr and
    (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)\<rbrace>
   maybe_sched_context_bind_tcb scptr tcbptr
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_sched_context_bind_tcb_def
  by (wpsimp wp: sched_context_bind_tcb_valid_sched get_tcb_obj_ref_wp)

lemma sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
    and (\<lambda>s. sc_tcb_sc_at (\<lambda>p. \<exists>tp. p = Some tp \<and> tp \<noteq> idle_thread s) sc_ptr s)\<rbrace>
     sched_context_unbind_tcb sc_ptr
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_tcb_def assert_opt_def)
  by (wpsimp wp: set_tcb_sched_context_valid_sched_except_blocked_None
                    tcb_release_remove_valid_blocked_except_set_const
                    tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                    tcb_sched_dequeue_valid_blocked_except_set
                    reschedule_required_valid_blocked_except_set)
     (fastforce simp: valid_sched_def sc_tcb_sc_at_def obj_at_def)

lemma maybe_sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
    and (\<lambda>s. \<forall>sc_ptr. bound_sc_tcb_at (\<lambda>x. x = Some sc_ptr) tcb_ptr s \<longrightarrow> sc_tcb_sc_at (\<lambda>p. \<exists>tp. p = Some tp \<and> tp \<noteq> idle_thread s) sc_ptr s)\<rbrace>
     maybe_sched_context_unbind_tcb tcb_ptr
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_sched_context_unbind_tcb_def
  apply (wpsimp wp: sched_context_unbind_tcb_valid_sched get_tcb_obj_ref_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma valid_sched_release_queue_update[simp]:
  "set queue = set (release_queue s) \<Longrightarrow> distinct queue \<Longrightarrow> distinct (release_queue s) \<Longrightarrow>
        sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) queue \<Longrightarrow>
        sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s) (release_queue s) \<Longrightarrow>
   valid_sched (s\<lparr>release_queue:=queue\<rparr>) = valid_sched s"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     sorted_release_q_def weak_valid_sched_action_def valid_blocked_def
                     not_in_release_q_def not_queued_def)

context DetSchedSchedule_AI begin

crunches install_tcb_cap
for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
and simple_sched_action[wp]: "simple_sched_action :: det_state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv simp: crunch_simps)

lemma install_tcb_frame_cap_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and invs\<rbrace> install_tcb_frame_cap a d f \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_frame_cap_def
  by (wpsimp wp: reschedule_valid_sched_const check_cap_inv hoare_drop_imp
                 thread_set_not_state_valid_sched)

lemma set_mcpriority_bound_sc_tcb_at[wp]:
  "set_mcpriority target a \<lbrace>bound_sc_tcb_at P target'\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp simp: thread_set_def wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma set_mcpriority_bound_sc_tcb_at_cur_thread[wp]:
  "set_mcpriority target a \<lbrace>(\<lambda>s. bound_sc_tcb_at P (cur_thread s) s)\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp simp: thread_set_def wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma set_mcpriority_not_cur_thread[wp]:
  "set_mcpriority target a \<lbrace>not_cur_thread target'\<rbrace>"
  unfolding set_mcpriority_def
  by (wpsimp simp: thread_set_def wp: set_object_wp)

crunch scheduler_act_not[wp]: set_priority "scheduler_act_not y"
  (wp: crunch_wps simp: crunch_simps)

crunch cur_thread[wp]: reorder_ntfn, reorder_ep "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma reorder_ntfn_bound_sc_tcb_at_cur_thread[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   reorder_ntfn a
   \<lbrace>\<lambda>_. \<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (rule_tac f="cur_thread" in hoare_lift_Pf; wpsimp)

lemma reorder_ep_bound_sc_tcb_at_cur_thread[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   reorder_ep a
   \<lbrace>\<lambda>_. \<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (rule_tac f="cur_thread" in hoare_lift_Pf; wpsimp)

lemma set_scheduler_action_bound_sc_tcb_at_cur_thread[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   set_scheduler_action sched_act
   \<lbrace>\<lambda>x s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (rule_tac f="cur_thread" in hoare_lift_Pf; wpsimp)

crunches set_priority, set_mcpriority
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_priority_bound_sc_tcb_at_cur_thread[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   set_priority param_a param_b
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>"
  by (rule_tac f="cur_thread" in hoare_lift_Pf;
      wpsimp simp: set_priority_def get_thread_state_def thread_get_def thread_set_priority_def
               wp: maybeM_inv reschedule_required_lift)

crunch simple_sched_action[wp]: sched_context_bind_tcb simple_sched_action
  (wp: crunch_wps simp: crunch_simps)

crunches set_mcpriority
  for active_sc_tcb_at[wp]: "active_sc_tcb_at a"

lemma set_mcpriority_budget_ready[wp]:
  "set_mcpriority target a \<lbrace>budget_ready t\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def dest!: get_tcb_SomeD)
  apply (safe; rule_tac x=scp in exI; fastforce)
  done

lemma set_mcpriority_budget_sufficient[wp]:
  "set_mcpriority target a \<lbrace>budget_sufficient t\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def dest!: get_tcb_SomeD)
  apply (safe; rule_tac x=scp in exI; fastforce)
  done

lemma tcc_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf (ThreadControlCaps target slot fault_handler timeout_handler
                                      croot vroot buffer)
    and ct_active and ct_ARS\<rbrace>
     invoke_tcb (ThreadControlCaps target slot fault_handler timeout_handler croot vroot buffer)
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: split_def cong: option.case_cong)
  apply wp
       \<comment> \<open>install_tcb_cap slot 2\<close>
       apply (wpsimp wp: install_tcb_frame_cap_valid_sched)
      \<comment> \<open>install_tcb_cap slot 1\<close>
      apply (clarsimp cong: conj_cong)
      apply (rule hoare_vcg_E_elim, wp)
      apply (wpsimp wp: install_tcb_cap_invs)
     \<comment> \<open>install_tcb_cap slot 0\<close>
     apply (clarsimp cong: conj_cong)
     apply (rule hoare_vcg_E_elim, wp)
     apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R hoare_vcg_all_lift
                 install_tcb_cap_invs
                 static_imp_wp static_imp_conj_wp
            | strengthen tcb_cap_always_valid_strg
            | wp install_tcb_cap_cte_wp_at_ep)+)[1]
    \<comment> \<open>install_tcb_cap slot 4\<close>
    apply (clarsimp cong: conj_cong)
    apply (rule hoare_vcg_E_elim, wp)
    apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R hoare_vcg_all_lift
                 install_tcb_cap_invs
                 static_imp_wp static_imp_conj_wp
           | strengthen tcb_cap_always_valid_strg
           | wp install_tcb_cap_cte_wp_at_ep)+)[1]
   \<comment> \<open>install_tcb_cap slot 3\<close>
   apply (clarsimp cong: conj_cong)
   apply (rule hoare_vcg_E_elim, wp)
   apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R hoare_vcg_all_lift
                 install_tcb_cap_invs
                 static_imp_wp static_imp_conj_wp
          | strengthen tcb_cap_always_valid_strg
          | wp install_tcb_cap_cte_wp_at_ep)+)[1]
  \<comment> \<open>resolve using precondition\<close>
  apply simp
  apply (strengthen tcb_cap_valid_ep_strgs)
  apply (clarsimp cong: conj_cong)
  apply (intro conjI impI;
         clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                 dest!: valid_vtable_root_is_arch_cap)
     apply (all \<open>clarsimp simp: is_cap_simps cte_wp_at_caps_of_state\<close>)
    apply (all \<open>clarsimp simp: obj_at_def is_tcb typ_at_eq_kheap_obj cap_table_at_typ\<close>)
  by auto

lemma set_irq_state_budget_conditions[wp]:
  "set_irq_state w x \<lbrace>(\<lambda>s. P (active_sc_tcb_at t s)):: det_state \<Rightarrow> _\<rbrace>"
  "set_irq_state w x \<lbrace>(\<lambda>s. P (budget_ready t s)):: det_state \<Rightarrow> _\<rbrace>"
  "set_irq_state w x \<lbrace>(\<lambda>s. P (budget_sufficient t s)):: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_irq_state_def)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: active_sc_tcb_at_defs)
  apply (wpsimp simp: set_irq_state_def)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: budget_ready_defs)
  apply (wpsimp simp: set_irq_state_def)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: budget_sufficient_defs)
  done

crunches empty_slot_ext, empty_slot
  for active_sc_tcb_at[wp]: "(\<lambda>s. P (active_sc_tcb_at t s)):: det_state \<Rightarrow> _"
  and budget_ready[wp]: "(\<lambda>s. P (budget_ready t s)):: det_state \<Rightarrow> _"
  and budget_sufficient[wp]: "(\<lambda>s. P (budget_sufficient t s)):: det_state \<Rightarrow> _"
  (wp:  ignore: set_irq_state)

crunches cancel_all_ipc
  for active_sc_tcb_at[wp]: "(\<lambda>s. (active_sc_tcb_at t s)):: det_state \<Rightarrow> _"
  and budget_ready[wp]: "(\<lambda>s. P (budget_ready t s)):: det_state \<Rightarrow> _"
  and budget_sufficient[wp]: "(\<lambda>s. P (budget_sufficient t s)):: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma restart_thread_if_no_fault_ct_in_state_neq:
  "\<lbrace>ct_in_state P and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   restart_thread_if_no_fault t
  \<lbrace>\<lambda>_. ct_in_state P :: det_state \<Rightarrow> _\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp wp: sts_ctis_neq)

lemma reply_unlink_tcb_ct_in_state_neq:
  "\<lbrace>ct_in_state P and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   reply_unlink_tcb t r
  \<lbrace>\<lambda>_. ct_in_state P :: det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: sts_ctis_neq gts_wp get_simple_ko_wp)

lemma cancel_all_ipc_ct_in_state[wp]:
  "\<lbrace>ct_active and valid_ep_q\<rbrace>
   cancel_all_ipc epptr
  \<lbrace>\<lambda>_. ct_active :: det_state \<Rightarrow> _\<rbrace>"
  unfolding cancel_all_ipc_def
  apply wpsimp
       apply (rule_tac I="ct_active and (\<lambda>s. \<forall>x. x \<in> set queue \<longrightarrow> x \<noteq> cur_thread s)" in mapM_x_inv_wp)
         apply clarsimp
        prefer 2
        apply (assumption)
       apply (wpsimp wp: restart_thread_if_no_fault_ct_in_state_neq gts_wp)
      apply (wpsimp wp: restart_thread_if_no_fault_ct_in_state_neq gts_wp)
     apply (wpsimp wp: get_ep_queue_wp)
    apply wpsimp
      apply (rule_tac I="ct_active and (\<lambda>s. \<forall>x. x \<in> set queue \<longrightarrow> x \<noteq> cur_thread s)" in mapM_x_inv_wp)
        apply clarsimp
       prefer 2
       apply (assumption)
      apply (wpsimp wp: restart_thread_if_no_fault_ct_in_state_neq gts_wp)
     apply (wpsimp wp: restart_thread_if_no_fault_ct_in_state_neq gts_wp)
    apply (wpsimp wp: get_ep_queue_wp)
   apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: valid_ep_q_def)
  apply (drule_tac x=epptr in spec)
  apply (fastforce)
  done

lemma install_tcb_cap_active_sc_tcb_at[wp]:
  "\<lbrace>invs and tcb_at target  and active_sc_tcb_at t \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. active_sc_tcb_at t :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_budget_ready[wp]:
  "\<lbrace>invs and tcb_at target and budget_ready t \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. budget_ready t :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_budget_sufficient[wp]:
  "\<lbrace>invs and tcb_at target and budget_sufficient t \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. budget_sufficient t :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_ct_active[wp]:
  "\<lbrace>invs and tcb_at target and ct_active and valid_ep_q\<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. ct_active :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  apply wpsimp
  apply (wpsimp wp: check_cap_inv )
  apply (simp)
  apply (rule valid_validE, rule cap_delete_fh_lift)
  apply wpsimp+
  apply assumption
  by clarsimp

crunches install_tcb_cap
  for cur_thread[wp]: "(\<lambda>s. P (cur_thread s)) :: det_state \<Rightarrow> _"
  (wp: crunch_wps preemption_point_inv check_cap_inv dxo_wp_weak)

lemma budget_RS_rewrite_helper:
  "bound_sc_tcb_at (\<lambda>p. \<exists>scp. is_refill_ready scp 0 s' \<and> p = Some scp) t s' = budget_ready t s'"
  "bound_sc_tcb_at (\<lambda>p. \<exists>scp. is_refill_sufficient scp 0 s' \<and> p = Some scp) t s' = budget_sufficient t s'"
  by (fastforce simp: budget_ready_defs)+

lemma tcs_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf (ThreadControlSched target slot fault_handler mcp priority sc)
    and ct_active and ct_ARS\<rbrace>
     invoke_tcb (ThreadControlSched target slot fault_handler mcp priority sc)
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: split_def cong: option.case_cong)
  apply (wp maybeM_wp_drop_None)
       \<comment> \<open>bind/unbind sched context\<close>
      apply (clarsimp cong: conj_cong)
      apply (wpsimp wp: maybe_sched_context_bind_tcb_valid_sched
                        maybe_sched_context_unbind_tcb_valid_sched, assumption)
     \<comment> \<open>set priority\<close>
     apply (clarsimp cong: conj_cong)
     apply (rule hoare_post_add[where R="\<lambda>_.valid_sched and simple_sched_action"])
     apply (clarsimp cong: conj_cong)
     apply (wpsimp wp: maybeM_wp_drop_None set_priority_valid_sched hoare_vcg_all_lift hoare_vcg_imp_lift)
      apply (wps, wpsimp)
     apply (clarsimp, assumption)
    \<comment> \<open>set mcpriority\<close>
    apply (wpsimp wp: maybeM_wp_drop_None)
     apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift
                        set_mcpriority_budget_ready
                        set_mcpriority_budget_sufficient
                        hoare_vcg_disj_lift
             | rule hoare_lift_Pf[where f = cur_thread])+)[1]
    apply (clarsimp, assumption)
   \<comment> \<open>install_tcb_cap\<close>
   apply (rule hoare_vcg_E_elim, wpsimp)
   apply (rule valid_validE_R)
   apply ((wpsimp simp: budget_RS_rewrite_helper
                    wp: hoare_vcg_disj_lift hoare_vcg_all_lift
                        install_tcb_cap_bound_sc_tcb_at static_imp_wp
          | rule valid_validE, wps, wpsimp wp: install_tcb_cap_bound_sc_tcb_at)+)[1]
  \<comment> \<open>resolve using preconditions\<close>
  apply (clarsimp cong: conj_cong)
  apply (intro conjI impI;
         clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                 dest!: valid_vtable_root_is_arch_cap)
     apply (erule valid_sched_implies_valid_ipc_qs)
    apply (case_tac x; simp)
   apply (case_tac x; simp)
  apply (case_tac priority; simp)
  apply (drule valid_sched_implies_valid_ipc_qs(1), simp)
  done

end

crunch not_cur_thread[wp]: reply_remove "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2)

(*
lemma reschedule_required_valid_blocked_except: not used either in Ainvs or Refine
 "\<lbrace>valid_blocked_except thread
   and (\<lambda>s. scheduler_action s = switch_thread thread)\<rbrace>
       reschedule_required \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked)
  apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except_set hoare_vcg_if_lift2
    hoare_drop_imp
           simp: tcb_sched_action_def)
defer
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked)

apply (intro conjI)
defer
apply (fastforce simp: valid_blocked_def valid_blocked_except_def)
apply (clarsimp simp: valid_blocked_except_def)

apply (clarsimp simp: etcb_at_def valid_blocked_except_def valid_blocked_def split: option.splits)
apply (safe; (clarsimp simp: pred_tcb_at_def obj_at_def)?)
*)

lemma awaken_ready_qs_helper:
  "\<lbrace>valid_ready_qs and K (distinct queue) and
    (\<lambda>s. \<forall>target\<in>set queue. (st_tcb_at runnable target
     and active_sc_tcb_at target and
     budget_ready target and
     budget_sufficient target) s)\<rbrace>
   mapM_x (\<lambda>t. do possible_switch_to t;
                  modify (reprogram_timer_update (\<lambda>_. True))
               od) queue
   \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (induct queue; clarsimp simp: mapM_append_single mapM_x_Nil mapM_x_Cons bind_assoc)
  by (wpsimp wp: hoare_vcg_ball_lift possible_switch_to_valid_ready_qs)

lemma awaken_valid_ready_qs:
  "\<lbrace>valid_ready_qs and valid_release_q\<rbrace> awaken \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  unfolding awaken_def
  unfolding fun_of_m_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_ready_qs_helper)
  apply (rule conjI)
   apply (clarsimp simp: valid_release_q_def intro!: distinct_takeWhile)
  apply clarsimp
  apply (drule set_takeWhileD)
  apply (clarsimp simp: valid_release_q_def)
  apply (drule_tac x=target in bspec, clarsimp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  apply (case_tac y; clarsimp simp: is_refill_ready_def is_refill_sufficient_def obj_at_def)
  done

lemma awaken_valid_sched_helper:
  notes set_scheduler_action_valid_ready_qs[wp del]
  shows
  "\<lbrace>valid_sched_except_blocked and K (distinct queue) and (\<lambda>s. idle_thread s \<notin> set queue)
   and valid_blocked_except_set (set queue) and (\<lambda>s. cur_thread s \<notin> set queue)
   and (\<lambda>s. \<forall>target \<in> set queue. ((st_tcb_at runnable target
                and active_sc_tcb_at target and not_in_release_q target and
                budget_ready target and budget_sufficient target) s ))\<rbrace>
         mapM_x (\<lambda>t. do possible_switch_to t;
                        modify (reprogram_timer_update (\<lambda>_. True))
                     od) queue \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (induct queue; clarsimp simp: mapM_append_single mapM_x_Nil mapM_x_Cons bind_assoc)
   apply wpsimp
   apply (clarsimp simp: valid_blocked_except_set_2_def valid_sched_def valid_blocked_def)
  by (wpsimp wp: possible_switch_to_valid_sched_except_blocked_inc hoare_vcg_ball_lift
                 possible_switch_to_valid_ready_qs)

lemma awaken_valid_sched:
  "\<lbrace>valid_sched and cur_tcb and valid_idle and
(\<lambda>s. active_sc_tcb_at (cur_thread s) s) and
   (\<lambda>s. cur_thread s \<in> set (release_queue s) \<longrightarrow> \<not> budget_ready (cur_thread s) s)\<rbrace>
   awaken \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding awaken_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_valid_sched_helper simp: valid_sched_def)
  apply (simp only: dropWhile_eq_drop[symmetric])
  apply (intro conjI) prefer 3
        apply (clarsimp simp: valid_sched_def valid_release_q_def intro!: distinct_takeWhile)
       prefer 6
       apply clarsimp
       apply (frule distinct_takeWhle[rotated], clarsimp)
       apply (clarsimp simp: not_in_release_q_def)
       apply (drule set_takeWhileD, clarsimp)
       apply (clarsimp simp: valid_release_q_def split: option.splits)
       apply (drule_tac x=target in bspec, clarsimp)
       apply (clarsimp split: option.splits simp: dropWhile_eq_drop[symmetric])
       apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
       apply (rename_tac ko ko'; case_tac ko; clarsimp)
       apply (rename_tac sc n)
       apply (frule_tac t=target and sc=sc and n=n in refill_ready_tcb_simp3, simp+)
       apply (clarsimp simp: tcb_ready_time_def refill_prop_defs get_tcb_rev obj_at_def
                      split: option.splits)
      apply (clarsimp simp: valid_release_q_def sorted_release_q_def)
      apply (rule conjI, clarsimp dest!: set_dropWhileD)
      apply (subgoal_tac "sorted_wrt (\<lambda>t t'. tcb_ready_time t s \<le> tcb_ready_time t' s)
                              (takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) (release_queue s)
                              @ dropWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) (release_queue s))")
       apply (simp only: sorted_wrt_append, simp)
     apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def dest!: set_dropWhileD)
    apply (clarsimp simp: not_in_release_q_def dest!: set_takeWhileD)
    apply (clarsimp simp: valid_release_q_def)
    apply (drule_tac x="idle_thread s" in bspec, simp, clarsimp)
    apply (drule (1) st_tcb_at_idle_thread, clarsimp)
   apply (clarsimp simp: valid_blocked_except_set_def valid_blocked_def dest!: set_dropWhileD)+
   apply (case_tac "t \<in> set (release_queue s)")
    prefer 2
    (* t is not in release_queue from the beginning *)
    apply (drule_tac x=t in spec, clarsimp simp: not_in_release_q_def)
    (* t is/was in release_queue *)
   apply (drule (1) distinct_not_in_takeWhile[rotated])
    apply (clarsimp simp: valid_release_q_def)
   apply (clarsimp simp: not_in_release_q_def dropWhile_eq_drop[symmetric])
  apply (clarsimp simp: get_tcb_rev cur_tcb_def active_sc_tcb_at_defs is_tcb
                 split: option.splits)
  apply (clarsimp dest!: set_takeWhileD)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (rename_tac sc n)
  apply (frule (2) refill_ready_tcb_simp3)
  by (clarsimp simp: is_refill_ready_def obj_at_def tcb_ready_time_def get_tcb_rev)

crunches awaken
for cur_tcb[wp]: cur_tcb
and budget_ready: "\<lambda>s. P (budget_ready t s)"
and budget_ready: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient: "\<lambda>s. P (budget_sufficient t s)"
and budget_ready_ct: "\<lambda>s. P (budget_ready (cur_thread s) s)"
and budget_sufficient_ct: "\<lambda>s. P (budget_sufficient (cur_thread s) s)"
and active_sc_tcb_at'[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
and active_sc_tcb_at_ct[wp]: "\<lambda>s. P (active_sc_tcb_at(cur_thread s) s)"
  (wp: hoare_drop_imps mapM_x_wp')

(* commit_time *)

crunches commit_domain_time
  for valid_ready_qs[wp]: valid_ready_qs
  and valid_release_q[wp]: valid_release_q
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ko_at[wp]: "\<lambda>s. ko_at P t s"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and kheap[wp]: "\<lambda>s. P (kheap s)"
  and ct_not_in_q[wp]: "\<lambda>s. ct_not_in_q s"
  and valid_sched_action[wp]: "\<lambda>s. valid_sched_action s"
  and valid_blocked[wp]: "\<lambda>s. valid_blocked s"
  and ct_in_cur_domain[wp]: "\<lambda>s. ct_in_cur_domain s"

lemma sc_consumed_update_sc_tcb_sc_at[wp]:
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

crunches commit_domain_time, refill_split_check
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain"
  and valid_idle_etcb[wp]: "valid_idle_etcb"
  and etcb_at[wp]: "etcb_at P t"
  (wp: crunch_wps set_refills_budget_ready simp: crunch_simps refill_full_def)

lemma commit_time_sc_tcb_sc_at[wp]:
  "commit_time \<lbrace>\<lambda>s. sc_tcb_sc_at P sc_ptr s\<rbrace>"
   unfolding commit_time_def
   by (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps
            simp: sc_refill_ready_def)

crunches commit_time
  for simple_sched_action[wp]: "simple_sched_action"
  and ct_not_in_q[wp]: "ct_not_in_q"
  (wp: crunch_wps simp: crunch_simps)
(*
lemma schedule_used_r_time:
  "r_time (hd (schedule_used ls new))
   = (case ls of [] \<Rightarrow> r_time new
       | r#rs \<Rightarrow> r_time r)"
  by (case_tac ls; clarsimp simp: Let_def)

lemma schedule_used_r_amount:
  "r_amount (hd (schedule_used ls new))
   = (case ls of [] \<Rightarrow> r_amount new
       | r#rs \<Rightarrow> (if rs = [] \<and> r_time new \<le> r_time r then r_amount r + r_amount new
                  else r_amount r))"
  by (case_tac ls; fastforce simp: Let_def)
*)

(* min_budget_merge
lemma min_budget_merge_sufficient_hd:
  "ls \<noteq> [] \<longrightarrow> MIN_BUDGET \<le> r_amount (hd ls) \<longrightarrow> r_amount (hd ls) \<le> refills_sum ls \<longrightarrow>
         MIN_BUDGET \<le> r_amount (hd (min_budget_merge b ls))"
  apply (clarsimp)
  apply (rule min_budget_merge_sufficient[rule_format]; simp)
  done

lemma min_budget_merge_sufficient_inv:
  "\<lbrakk>0 < length ls; sufficient_refills 0 ls;
    r_amount (hd ls) \<le> refills_sum ls\<rbrakk>
      \<Longrightarrow> sufficient_refills 0 (min_budget_merge b ls)"
  by (clarsimp simp: sufficient_refills_def refills_capacity_def MIN_REFILLS_def)
     (rule min_budget_merge_sufficient_hd[rule_format, rotated]; clarsimp?)

lemma update_min_budget_merge_sufficient:
  "\<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s
      \<and> obj_at (\<lambda>p. \<exists>sc n. p = SchedContext sc n
                  \<and> 0 < length (sc_refills sc)
                  \<and> r_amount (refill_hd sc) \<le> refills_sum (sc_refills sc)) sc_ptr s\<rbrace>
   update_sched_context sc_ptr (sc_refills_update (min_budget_merge full))
   \<lbrace>\<lambda>_ s. budget_sufficient (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)
  apply (intro conjI impI; clarsimp?)
  apply (rule_tac x=scp in exI; clarsimp)
  by (rule min_budget_merge_sufficient_inv; clarsimp?)

(* FIXME maybe move? *)
lemma min_budget_merge_r_time[rule_format]:
  "ls \<noteq> [] \<longrightarrow> sorted_wrt (\<lambda>r r'. r_time r \<le> r_time r') ls \<longrightarrow>
       r_time (hd (min_budget_merge b ls)) \<ge> r_time (hd ls)"
  apply (induction ls arbitrary: b rule: length_induct; clarsimp)
  apply (rename_tac ls b, case_tac ls, simp)
  apply (rename_tac list, case_tac list; clarsimp)
  apply (drule_tac x="aa\<lparr>r_amount := r_amount a + r_amount aa\<rparr> # lista" in spec, clarsimp)
  by (drule_tac x=False in spec, fastforce)
*)
lemma refill_budget_check_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_budget_check_def
  supply if_split [split del]
  apply (wpsimp wp: set_refills_valid_sched_action_act_not
                    refill_ready_wp is_round_robin_wp refill_full_wp
              simp: Let_def)
  done

lemma refill_budget_check_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: set_refills_valid_ready_qs
                    refill_ready_wp is_round_robin_wp refill_full_wp
              simp: Let_def split_del: if_split)
  by (fastforce simp: active_sc_tcb_at_defs valid_ready_qs_def in_queue_2_def not_queued_def)

(* this is for the call from commit_time, with the assert *)
lemma refill_budget_check_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. is_refill_sufficient (cur_sc s) usage s) \<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: set_refills_valid_ready_qs
                    refill_ready_wp is_round_robin_wp refill_full_wp
              simp: Let_def split_del: if_split)
apply (clarsimp simp: sufficient_refills_defs refill_prop_defs obj_at_def MIN_BUDGET_nonzero
split: if_split_asm  split del: if_split)
  apply (intro conjI impI allI;
         clarsimp simp: valid_ready_qs_def in_queue_2_def pred_tcb_at_def obj_at_def;
         drule_tac x=d and y=p in spec2; clarsimp; drule_tac x=tcb_ptr in bspec, simp;
         clarsimp simp: refill_prop_defs sufficient_refills_defs obj_at_def MIN_REFILLS_def;
         fastforce?; (clarsimp simp: MIN_BUDGET_nonzero not_less)?)
  apply (intro conjI impI allI; clarsimp?)
  sorry (* waiting for the spec update; will need more preconditions *)

lemma refill_budget_check_valid_release_q_not_in_release_q:
  "\<lbrace>valid_release_q and (\<lambda>s. sc_not_in_release_q (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding refill_budget_check_def
  supply if_split [split del]
  by (wpsimp wp: set_refills_valid_release_q_not_in_release_q
                 refill_ready_wp is_round_robin_wp refill_full_wp
           simp: Let_def)

(* if the new refill_budget_check always leaves one refill only that is ready and sufficient,
 then both valid_release_q and valid_ready_qs should be preserved *)
lemma refill_budget_check_valid_release_q:
  "\<lbrace>valid_release_q\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding refill_budget_check_def
(*  by (wpsimp wp: set_refills_valid_release_q
                    refill_ready_wp is_round_robin_wp refill_full_wp
 simp: Let_def split_del: if_split)
     (intro conjI impI allI; clarsimp simp: pred_tcb_at_def obj_at_def) *) sorry

lemma update_sched_context_ko_at_Endpoint[wp]:
    "update_sched_context ptr f
    \<lbrace>\<lambda>s. P (ko_at (Endpoint reply_obj) reply_ptr s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp simp: obj_at_def)
  done

lemma sc_consumed_update_tcb_ready_time[wp]:
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: tcb_ready_time_def obj_at_def elim!: rsubst[where P=P])
  apply (clarsimp split: option.splits dest!: get_tcb_SomeD simp: get_tcb_def)
  done

lemma sc_consumed_update_valid_queues[wp]:
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>valid_release_q\<rbrace>"
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>valid_ready_qs\<rbrace>"
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>valid_ep_q\<rbrace>"
  apply (wpsimp wp: valid_release_q_lift active_sc_tcb_at_update_sched_context_no_change)
  apply (wpsimp wp: valid_ready_qs_lift active_sc_tcb_at_update_sched_context_no_change
                    budget_ready_update_sched_context_no_change
                    budget_sufficient_update_sched_context_no_change)
  apply (wpsimp wp: valid_ep_q_lift hoare_vcg_disj_lift active_sc_tcb_at_update_sched_context_no_change
                    budget_ready_update_sched_context_no_change
                    budget_sufficient_update_sched_context_no_change)
  done

lemma commit_time_valid_release_q:
  "\<lbrace>valid_release_q and cur_sc_in_release_q_imp_zero_consumed\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps
                  set_refills_valid_release_q
                  refill_budget_check_valid_release_q)

lemma commit_time_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imp
                     set_refills_valid_ready_qs refill_budget_check_valid_ready_qs)
    apply (clarsimp simp: obj_at_def sufficient_refills_defs MIN_BUDGET_nonzero split: if_split_asm)
(*   by (fastforce simp: active_sc_tcb_at_defs valid_ready_qs_def refill_prop_defs in_queue_2_def obj_at_def)*)
sorry

lemma commit_time_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                  hoare_vcg_all_lift hoare_drop_imps set_refills_valid_sched_action_act_not
                  refill_budget_check_valid_sched_action_act_not
        | strengthen simple_sched_act_not)+

lemma commit_time_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                     hoare_vcg_all_lift hoare_drop_imps)

crunches commit_domain_time, refill_budget_check
  for valid_blocked_except_set[wp]: "valid_blocked_except_set S"
  and valid_blocked[wp]: "valid_blocked"
  (wp: crunch_wps simp: crunch_simps)

lemma commit_time_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_idle_etcb :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                     hoare_vcg_all_lift hoare_drop_imps)

lemma commit_time_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_blocked_except_set S :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps update_sched_context_valid_blocked_except_set)

lemma commit_time_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
   unfolding valid_sched_def
   apply (wpsimp wp: commit_time_ct_in_cur_domain commit_time_valid_release_q
                  commit_time_valid_idle_etcb commit_time_valid_blocked_except_set
                  commit_time_valid_ready_qs commit_time_valid_sched_action
            simp: pred_tcb_at_def obj_at_def)
  by (drule_tac x=t in spec, clarsimp)

crunches commit_time
  for not_queued[wp]: "not_queued t"
  and not_in_release_q[wp]: "not_in_release_q t"
  and ct_not_in_release_q[wp]: "ct_not_in_release_q"
  (wp: crunch_wps hoare_drop_imps simp: crunch_simps)

lemma refill_ready_kh_move_time:
  "refill_ready_kh (curtime - t) scp 0 kh = refill_ready_kh curtime scp t kh"
  unfolding refill_ready_kh_def
  by (clarsimp simp: split: option.splits kernel_object.splits)

(* end commit_time *)

(* refill_unblock_check *)

lemma r_time_hd_refills_merge_prefix:
  "r_time (hd (refills_merge_prefix (a # l))) = r_time a"
  by (induct l arbitrary: a;
      clarsimp simp: merge_refill_def)

(* can this be done with valid_refills, cur_time \<le> time (hd (refills)), instead of valid_machine_time ? *)
lemma refill_unblock_check_budget_ready[wp]:
  "\<lbrace>budget_ready tcb_ptr and valid_machine_time\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_ready tcb_ptr s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_refill_ready_def)
  apply (intro conjI impI, fastforce)
  apply (clarsimp simp: r_time_hd_refills_merge_prefix)
  apply (rule_tac x=scp in exI; clarsimp)
  apply (rule cur_time_no_overflow, simp)
  done

lemma refill_unblock_check_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient tcb_ptr\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_sufficient tcb_ptr s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_refill_sufficient_def
                        sufficient_refills_def refills_capacity_def)
  sorry \<comment> \<open>need to say that if MIN_BUDGET \<le> r_amount hd, then after performing refills_merge_prefix,
             we have that MIN_BUDGET \<le> r_amount hd\<close>

lemma refill_unblock_check_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)

crunch ready_queues[wp]: refill_unblock_check "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps simp: crunch_simps)

crunch release_queue[wp]: refill_unblock_check "\<lambda>s. P (release_queue s)"
  (wp: crunch_wps simp: crunch_simps)

lemma refill_unblock_check_etcb_at:
  "\<lbrace> etcb_at P x\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r. etcb_at P x\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  by (clarsimp simp: etcb_at'_def etcbs_of'_def)

lemma refill_unblock_check_active_sc_tcb_at[wp]:
  "\<lbrace> active_sc_tcb_at x\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r. active_sc_tcb_at x\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  by (fastforce simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                        test_sc_refill_max_def)

lemma refill_unblock_check_valid_ready_qs[wp]:
  "\<lbrace> valid_ready_qs and valid_machine_time\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: valid_ready_qs_def is_etcb_at_etcbs_of_tcb_at)
  apply (wpsimp simp: Ball_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_etcb_at
                      refill_unblock_check_active_sc_tcb_at)
  done

lemma tcb_ready_time_kh_sc_update_not_in:
  "\<lbrakk>bound_sc_tcb_at (\<lambda>p. p \<noteq> (Some sc_ptr)) t s; active_sc_tcb_at t s;
    kheap s sc_ptr = Some (SchedContext sc' n) \<rbrakk>
       \<Longrightarrow> tcb_ready_time_kh t (kheap s(sc_ptr \<mapsto> SchedContext sc n)) = tcb_ready_time t s"
  by (fastforce simp: active_sc_tcb_at_defs tcb_ready_time_kh_def tcb_ready_time_def get_tcb_rev
                 split: option.splits)

lemma refill_unblock_check_valid_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (clarsimp simp: refill_unblock_check_def)
     (wpsimp wp: get_refills_wp refill_ready_wp is_round_robin_wp
                 set_refills_valid_release_q_not_in_release_q)

lemma refill_unblock_check_st_tcb_at:
  "\<lbrace>\<lambda>s. st_tcb_at P (cur_thread s) s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. st_tcb_at P (cur_thread s) s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma refill_unblock_check_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: valid_blocked_except_set_def)
  apply (drule_tac x=t in spec, clarsimp simp: obj_at_def)
  apply (subgoal_tac "st \<noteq> Running \<and> st \<noteq> Restart \<or> \<not> active_sc_tcb_at t s")
   apply (erule_tac Q="\<not> active_sc_tcb_at t s" in disjE)
    apply (clarsimp simp: )
   apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                         active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_def obj_at_kh_def
                         test_sc_refill_max_kh_def test_sc_refill_max_def
                   split: if_splits)
  apply (drule_tac x=st in spec, clarsimp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def
                 split: if_splits)
  done

lemmas refill_unblock_check_valid_blocked[wp] =
       refill_unblock_check_valid_blocked_except_set[where S="{}"]

crunches refill_unblock_check
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain"
  and sc_at_period[wp]: "sc_at_period P p"
  and sc_at_period_sc[wp]: "\<lambda>s. sc_at_period P (cur_sc s) s"
    (wp: crunch_wps simp: crunch_simps)

lemma refill_unblock_check_sc_is_round_robin[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin p s)\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_is_round_robin p s)\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
     (clarsimp simp: sc_is_round_robin_def obj_at_def)

lemma refill_unblock_check_in_cur_domain:
  "\<lbrace>in_cur_domain t\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. in_cur_domain t\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: in_cur_domain_def etcb_at'_def etcbs_of'_def)
  done

lemma refill_unblock_check_in_cur_domain_cur_thread:
  "\<lbrace>\<lambda>s. in_cur_domain (cur_thread s) s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. in_cur_domain (cur_thread s) s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: in_cur_domain_def etcb_at'_def etcbs_of'_def)
  done

lemma refill_unblock_check_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and valid_machine_time\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (clarsimp simp: is_activatable_def weak_valid_sched_action_def switch_in_cur_domain_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_active_sc_tcb_at
                    refill_unblock_check_st_tcb_at refill_unblock_check_in_cur_domain)
  done

lemma refill_unblock_check_valid_sched:
  "\<lbrace>valid_sched and sc_not_in_release_q a and valid_machine_time\<rbrace>
    refill_unblock_check a \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: refill_unblock_check_valid_ready_qs refill_unblock_check_valid_release_q
                 refill_unblock_check_valid_sched_action refill_unblock_check_ct_in_cur_domain
                 refill_unblock_check_etcb_at)

lemma refill_unblock_check_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q scp\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. sc_not_in_release_q scp\<rbrace>"
   unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def not_in_release_q_def split: if_splits)

lemma refill_unblock_check_sc_not_in_ready_q[wp]:
  "\<lbrace>sc_not_in_ready_q scp\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. sc_not_in_ready_q scp\<rbrace>"
   unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def not_queued_def split: if_splits)

lemma refill_unblock_check_sc_not_in_release_q_ct[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_release_q (cur_sc s) s\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. sc_not_in_release_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma refill_unblock_check_sc_not_in_ready_q_ct[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_ready_q (cur_sc s) s\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma refill_unblock_check_sc_is_round_robin_ct[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma refill_unblock_check_zero_consumed[wp]:
  "\<lbrace>\<lambda>s. sc_ptr \<noteq> cur_sc s \<and> cur_sc_in_release_q_imp_zero_consumed s\<rbrace>
  refill_unblock_check sc_ptr
   \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  unfolding refill_unblock_check_def is_round_robin_def refill_ready_def
  apply (clarsimp simp: bind_assoc)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_period sc = sc_budget sc"; clarsimp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wp|wpc)+
      apply (wpsimp wp: hoare_vcg_all_lift get_refills_wp set_refills_wp)+
  apply (clarsimp simp: pred_tcb_at_def)
  apply (rename_tac tp sc n)
  apply (drule_tac x=tp in spec, clarsimp simp: obj_at_def split: if_split_asm)
  done

(* end refill_unblock_check *)

lemma sc_is_round_robin_reprogram_timer_update[simp]:
  "sc_is_round_robin p (s\<lparr>reprogram_timer := b\<rparr>)
          = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

context DetSchedSchedule_AI begin

lemma switch_sched_context_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and ct_not_in_release_q and ct_not_queued
     and valid_state
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s)
     and valid_machine_time\<rbrace>
   switch_sched_context
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: switch_sched_context_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp simp: bind_assoc)
(*
  apply (wpsimp wp: hoare_drop_imps commit_time_valid_sched[where budget=budget] refill_unblock_check_valid_sched)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def cong: conj_cong)
*)
  apply (wpsimp wp: hoare_drop_imps commit_time_valid_sched)
      apply (wpsimp wp: hoare_drop_imps rollback_time_valid_sched split_del: if_split)
     apply wpsimp+
     apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp)
      apply (wpsimp wp: refill_unblock_check_valid_sched)
     apply (rule_tac Q="\<lambda>rv s. \<not> reprogram_timer s \<longrightarrow>
                              (valid_sched and simple_sched_action and rollback_safe) s"
             in hoare_strengthen_post)
      apply (wpsimp wp: refill_unblock_check_valid_sched hoare_vcg_imp_lift)
     apply clarsimp
    apply wpsimp+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def rollback_safe_def cong: conj_cong)
  apply (subgoal_tac "sym_refs (state_refs_of s)")
   apply (drule sym[where s="Some _" and t="tcb_sched_context _"])
   apply (frule (1) ARM.sym_ref_tcb_sc, simp, clarsimp)
   apply (frule_tac tp=tp in ARM.sym_ref_tcb_sc, simp, simp)
   apply (clarsimp simp: valid_state_def valid_pspace_def)+
  done

lemma set_next_timer_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_timer_interrupt thread_time \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_next_timer_interrupt_def)
  by wpsimp

lemma set_next_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_interrupt \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_next_interrupt_def)
  by (wpsimp wp: hoare_drop_imp)

lemma sc_and_timer_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and ct_not_in_release_q and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s)
     and valid_state and cur_tcb
     and valid_machine_time\<rbrace>
   sc_and_timer
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sc_and_timer_def)
  by (wpsimp simp: wp: switch_sched_context_valid_sched)

(*
we know that after calling awaken,
all threads in the release queue are either not sufficient or ready
the current thread can be in the release queue
*)

lemma schedule_tcb_sched_enqueue_helper:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at
            (\<lambda>p. \<exists>scp. p = Some scp \<and>
                        is_refill_ready scp 0 s \<and>
                        is_refill_sufficient scp 0 s)
            candidate s\<rbrace>
      tcb_sched_action tcb_sched_enqueue ct
       \<lbrace>\<lambda>rv s.
           bound_sc_tcb_at
            (\<lambda>p. \<exists>scp. p = Some scp \<and>
                        is_refill_ready scp 0 s \<and>
                        is_refill_sufficient scp 0 s)
            candidate s\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def)

lemma enqueue_thread_queued_ct:
  "\<lbrace>\<lambda>s. thread = cur_thread s \<and>
      bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp 0 s \<and> is_refill_sufficient scp 0 s)) thread s\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. cur_thread s \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def obj_at_def pred_tcb_at_def
                        is_refill_ready_def is_refill_sufficient_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

lemma cur_sc_tcb_rev:
  "\<lbrakk>cur_sc_tcb s; sym_refs (state_refs_of s); scheduler_action s = resume_cur_thread\<rbrakk>
     \<Longrightarrow> bound_sc_tcb_at ((=) (Some (cur_sc s))) (cur_thread s) s"
  by (clarsimp simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
     (drule (2) sym_ref_sc_tcb, clarsimp simp: pred_tcb_at_def obj_at_def)

crunches schedule_choose_new_thread
  for simple_sched_action[wp]: simple_sched_action

lemma sc_is_round_robin_sa_update[simp]:
  "sc_is_round_robin t (s\<lparr>scheduler_action :=sa\<rparr>) = sc_is_round_robin t s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma sc_is_round_robin_rdq_update[simp]:
  "sc_is_round_robin t (s\<lparr>ready_queues :=rdq\<rparr>) = sc_is_round_robin t s"
  by (clarsimp simp: sc_is_round_robin_def)

crunches set_scheduler_action, tcb_sched_action
  for cur_sc_in_release_q_imp_zero_consumed[wp]: cur_sc_in_release_q_imp_zero_consumed
  and sc_is_round_robin[wp]: "\<lambda>s. P (sc_is_round_robin p s)"
  and sc_is_round_robin_cur[wp]: "\<lambda>s. P (sc_is_round_robin (cur_sc s) s)"
    (wp: crunch_wps simp: crunch_simps)

lemma valid_refills_cur_thread_update[simp]:
  "valid_refills ptr (s\<lparr>cur_thread := param_a\<rparr>) = valid_refills ptr s"
  by (clarsimp simp: valid_refills_def)

lemma valid_refills_domain_list_update[simp]:
  "valid_refills ptr (s\<lparr>domain_list := param_a\<rparr>) = valid_refills ptr s"
  by (clarsimp simp: valid_refills_def)

lemma valid_refills_cur_domain_update[simp]:
  "valid_refills ptr (s\<lparr>cur_domain := param_a\<rparr>) = valid_refills ptr s"
  by (clarsimp simp: valid_refills_def)

lemma valid_refills_domain_index_update[simp]:
  "valid_refills ptr (s\<lparr>domain_index := param_a\<rparr>) = valid_refills ptr s"
  by (clarsimp simp: valid_refills_def)

lemma sc_at_period_cur_thread_update[simp]:
  "sc_at_period P p (s\<lparr>cur_thread := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_domain_list_update[simp]:
  "sc_at_period P p (s\<lparr>domain_list := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_cur_domain_update[simp]:
  "sc_at_period P p (s\<lparr>cur_domain := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_domain_index_update[simp]:
  "sc_at_period P p (s\<lparr>domain_index := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_is_round_robin_cur_thread_update[simp]:
  "sc_is_round_robin p (s\<lparr>cur_thread := param_a\<rparr>) = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma sc_is_round_robin_release_queue_update[simp]:
  "sc_is_round_robin p (s\<lparr>release_queue := param_a\<rparr>) = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

crunches switch_to_idle_thread, guarded_switch_to, switch_to_thread
  for cur_sc_in_release_q_imp_zero_consumed[wp]: "cur_sc_in_release_q_imp_zero_consumed::det_state \<Rightarrow> _"
    (wp: crunch_wps simp: crunch_simps)

crunches next_domain
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
    (wp: crunch_wps dxo_wp_weak simp: crunch_simps)

lemma next_domain_sc_at_period[wp]:
  "\<lbrace>sc_at_period P p\<rbrace> next_domain \<lbrace>\<lambda>_. sc_at_period P p\<rbrace>"
  apply (clarsimp simp: next_domain_def)
  apply (wpsimp wp: dxo_wp_weak simp: sc_at_period_def)
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def etcb_at_def active_sc_tcb_at_defs)
  done

lemma next_domain_sc_at_period_cur:
  "\<lbrace>\<lambda>s. sc_at_period P (cur_sc s) s\<rbrace> next_domain \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
  apply (clarsimp simp: next_domain_def)
  apply (wpsimp wp: dxo_wp_weak simp: sc_at_period_def)
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def etcb_at_def active_sc_tcb_at_defs)
  done

lemma next_domain_sc_is_round_robin[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin p s)\<rbrace> next_domain \<lbrace>\<lambda>_. \<lambda>s. P (sc_is_round_robin p s)\<rbrace>"
  apply (clarsimp simp: next_domain_def)
  apply (wpsimp wp: dxo_wp_weak simp: sc_is_round_robin_def)
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def etcb_at_def active_sc_tcb_at_defs)
  done

lemma next_domain_sc_is_round_robin_cur[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace> next_domain \<lbrace>\<lambda>_. \<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

crunches schedule_choose_new_thread, switch_to_thread, set_scheduler_action, tcb_sched_action
  for cur_sc_in_release_q_imp_zero_consumed[wp]: "cur_sc_in_release_q_imp_zero_consumed::det_state \<Rightarrow> _"
  and sc_at_period[wp]: "sc_at_period P p::det_state \<Rightarrow> _"
  and cur_sc[wp]: "\<lambda>s::det_state. P (cur_sc s)"
  and valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  and sc_is_round_robin[wp]: "\<lambda>s::det_state. P (sc_is_round_robin p s)"
    (wp: crunch_wps dxo_wp_weak simp: crunch_simps Let_def)

lemma sc_is_round_robin_cur[wp]:
  "schedule_choose_new_thread \<lbrace>\<lambda>s::det_state. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  "switch_to_thread t \<lbrace>\<lambda>s::det_state. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)+

crunches set_scheduler_action, tcb_sched_action
  for sc_at_period_cur_sc[wp]: "\<lambda>s::det_state. sc_at_period P (cur_sc s) s"

lemma schedule_choose_new_thread_sc_at_period_cur[wp]:
  "\<lbrace>\<lambda>s::det_state. sc_at_period P (cur_sc s) s\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma switch_to_thread_sc_at_period_cur[wp]:
  "\<lbrace>\<lambda>s::det_state. sc_at_period P (cur_sc s) s\<rbrace> switch_to_thread t \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma refill_ready_weaken_margin:
  "is_refill_ready t k s \<Longrightarrow>
   l \<le> k \<Longrightarrow>
   k \<le> cur_time s \<Longrightarrow>
   l \<le> cur_time s \<Longrightarrow>
   cur_time s \<le> cur_time s + kernelWCET_ticks \<Longrightarrow>
   is_refill_ready t l s"
  apply (clarsimp simp: is_refill_ready_def obj_at_def)
  apply (erule order.trans)
  apply (rule word_plus_mono_left)
  apply (rule word_le_minus_mono_right)
  apply (simp)+
  apply (subst olen_add_eqv)
  apply (simp add: algebra_simps)
  apply (rule word_le_minus_mono_left)
  apply clarsimp+
  done

lemma schedule_valid_sched_helper:
"\<lbrace> cur_tcb and valid_sched and valid_idle
     and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)
     and (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> (\<not> budget_ready (cur_thread s) s))
     and (\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s)
     and (\<lambda>s. budget_sufficient (cur_thread s) s) and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s.  \<not> sc_is_round_robin (cur_sc s) s)
     and valid_machine_time and invs\<rbrace>
   do ct <- gets cur_thread;
      inq <- gets $ in_release_queue ct;
      ct_schedulable <- is_schedulable ct inq;
      action <- gets scheduler_action;
      case action of resume_cur_thread \<Rightarrow> do id <- gets idle_thread;
                                             assert (ct_schedulable \<or> ct = id);
                                             return ()
                                          od
      | switch_thread candidate \<Rightarrow>
          do when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);
             it <- gets idle_thread;
             target_prio <- thread_get tcb_priority candidate;
             ct_prio <- if ct \<noteq> it then thread_get tcb_priority ct else return 0;
             fastfail <- schedule_switch_thread_fastfail ct it ct_prio target_prio;
             cur_dom <- gets cur_domain;
             highest <- gets (is_highest_prio cur_dom target_prio);
             if fastfail \<and> \<not> highest then do tcb_sched_action tcb_sched_enqueue candidate;
                                              set_scheduler_action choose_new_thread;
                                              schedule_choose_new_thread
                                           od
             else if ct_schedulable \<and> ct_prio = target_prio then do tcb_sched_action tcb_sched_append candidate;
                   set_scheduler_action choose_new_thread;
                   schedule_choose_new_thread
                                                                  od
                  else do guarded_switch_to candidate;
                          set_scheduler_action resume_cur_thread
                       od
          od
      | choose_new_thread \<Rightarrow> do when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);
                                schedule_choose_new_thread
                             od;
      sc_and_timer
   od
  \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (simp, rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac action)
  apply (case_tac action; clarsimp)
    (* resume_cur_thread *)
    apply (wpsimp wp: sc_and_timer_valid_sched)
    apply (clarsimp simp: invs_def is_schedulable_bool_def get_tcb_def cur_tcb_def obj_at_def is_tcb_def
                   split: option.splits
                   dest!: get_tcb_SomeD)
    apply ((*rename_tac ko sc n;*) case_tac ko; clarsimp)
    apply (intro conjI impI; clarsimp simp: not_in_release_q_def)
     apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_release_q_def)
    apply (intro conjI impI; clarsimp simp: not_in_release_q_def)
    apply (clarsimp simp: valid_release_q_def valid_sched_def)
    apply (drule_tac x="idle_thread s" in bspec, simp, clarsimp)
    apply (drule (1) st_tcb_at_idle_thread, clarsimp)
    (* switch_thread *)
   apply (rename_tac candidate)
   apply (case_tac ct_schedulable; clarsimp)
    (* ct is schedulable *)
    apply (wp del: hoare_when_wp
              add: schedule_choose_new_thread_valid_sched
                   schedule_choose_new_thread_ct_not_in_release_q
                   schedule_choose_new_thread_ct_not_queued
                   sc_and_timer_valid_sched)
               apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
               apply wpsimp+
              apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and>
                                       scheduler_action s = choose_new_thread \<and> ct_in_q s \<and>
                                       simple_sched_action s \<and>
                                       (valid_idle and valid_ready_qs and valid_release_q) s \<and>
                                       cur_sc_in_release_q_imp_zero_consumed s \<and>
                                       (\<not> sc_is_round_robin (cur_sc s) s) \<and>
                                       valid_machine_time s \<and> invs s" in hoare_strengthen_post[rotated])
               apply clarsimp
              apply (wpsimp wp: hoare_vcg_conj_lift)
               apply (rule set_scheduler_action_valid_blocked_const)
              apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
             apply (rule_tac Q="\<lambda>_ s. scheduler_action s = switch_thread candidate
                    \<and> in_ready_q candidate s \<and> ct_in_q s
                    \<and> valid_sched s \<and> invs s
                    \<and> cur_sc_in_release_q_imp_zero_consumed s
                    \<and> valid_machine_time s
                    \<and> (\<not> sc_is_round_robin (cur_sc s) s)" in hoare_strengthen_post)
              apply (wpsimp wp: tcb_sched_enqueue_ct_in_q
                                enqueue_thread_queued[simplified in_ready_q_def[symmetric], simplified])
             apply (clarsimp simp: valid_sched_def)
            apply (wp schedule_choose_new_thread_valid_sched
                      schedule_choose_new_thread_ct_not_in_release_q
                      schedule_choose_new_thread_ct_not_queued)+
               apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s"
                       in hoare_strengthen_post[rotated], simp)
               apply wpsimp+
              apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and> scheduler_action s = choose_new_thread \<and>
                                        ct_in_q s \<and> simple_sched_action s \<and>
                                        (valid_idle and valid_ready_qs and valid_release_q) s \<and>
                                        cur_sc_in_release_q_imp_zero_consumed s \<and>
                                        (\<not> sc_is_round_robin (cur_sc s) s) \<and>
                                        valid_machine_time s \<and> invs s"
                               in hoare_strengthen_post[rotated])
               apply (clarsimp simp: invs_def)
              apply (wpsimp wp: set_scheduler_action_obvious set_scheduler_action_valid_blocked_const)+
             apply (wpsimp wp: tcb_sched_append_valid_blocked_except_set_const)
             apply (rule_tac Q="\<lambda>_ s. scheduler_action s = switch_thread candidate \<and>
                                      in_ready_q candidate s \<and> ct_in_q s \<and>
                                      valid_sched s \<and> invs s \<and> cur_sc_in_release_q_imp_zero_consumed s \<and>
                                      valid_machine_time s \<and>
                                      ( \<not> sc_is_round_robin (cur_sc s) s)"
                            in hoare_strengthen_post[rotated])
              apply (clarsimp simp: valid_sched_def)
             apply (wpsimp wp: tcb_sched_append_ct_in_q
                               append_thread_queued[simplified in_ready_q_def[symmetric], simplified])
            apply (wpsimp wp: guarded_switch_to_lift switch_to_thread_valid_sched
                              set_scheduler_action_rct_valid_sched_ct
                              stt_activatable[simplified ct_in_state_def]
                              hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                              switch_to_thread_sched_act_is_cur
                              switch_to_thread_ct_not_in_release_q switch_to_thread_invs)+
             apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
             apply wpsimp+
            apply (wpsimp wp: guarded_switch_to_lift switch_to_thread_valid_sched
                              set_scheduler_action_rct_valid_sched_ct
                              stt_activatable[simplified ct_in_state_def]
                              hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                              switch_to_thread_sched_act_is_cur
                              switch_to_thread_ct_not_in_release_q switch_to_thread_invs)+
    (* discard result of fastfail calculation *)
         apply (strengthen valid_blocked_except_set_weaken)
         apply (wpsimp wp: hoare_drop_imp)+
      apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const
                        tcb_sched_enqueue_cur_ct_in_q hoare_drop_imp
                        schedule_tcb_sched_enqueue_helper)+
    apply (clarsimp simp: simple_sched_action_def cong: conj_cong)
    apply (clarsimp simp: not_cur_thread_def valid_sched_def is_schedulable_bool_def simple_sched_action_def
                          cur_tcb_def active_sc_tcb_at_defs is_tcb get_tcb_rev not_in_release_q_def
                          valid_sched_action_def weak_valid_sched_action_def switch_in_cur_domain_def
                   split: option.splits)
    (* ct is not schedulable *)
   apply (wp del: hoare_when_wp
             add: schedule_choose_new_thread_valid_sched
                  schedule_choose_new_thread_ct_not_in_release_q
                  schedule_choose_new_thread_ct_not_queued
                  sc_and_timer_valid_sched)
             apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
             apply wpsimp+
            apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and>
                                      scheduler_action s = choose_new_thread \<and> ct_in_q s \<and>
                                      simple_sched_action s \<and>
                                      (valid_idle and valid_ready_qs and valid_release_q) s \<and>
                                      cur_sc_in_release_q_imp_zero_consumed s \<and>
                                      ( \<not> sc_is_round_robin (cur_sc s) s) \<and>
                                      valid_machine_time s \<and> invs s"
                          in hoare_strengthen_post[rotated])
             apply clarsimp
            apply (rule hoare_vcg_conj_lift)
             apply (rule set_scheduler_action_valid_blocked_const)
            apply (wpsimp wp: set_scheduler_action_obvious)
           apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const tcb_sched_enqueue_ct_in_q enqueue_thread_queued)
           apply (rule_tac Q="\<lambda>_ s. scheduler_action s = switch_thread candidate \<and>
                                    in_ready_q candidate s \<and> ct_in_q s \<and>
                                    valid_sched s \<and> invs s \<and>
                                    cur_sc_in_release_q_imp_zero_consumed s \<and>
                                    (\<not> sc_is_round_robin (cur_sc s) s) \<and>
                                    valid_machine_time s"
                           in hoare_strengthen_post[rotated])
            apply (clarsimp simp: valid_sched_def)
           apply (wpsimp wp: tcb_sched_enqueue_ct_in_q
                             enqueue_thread_queued[simplified in_ready_q_def[symmetric], simplified])+
           apply (wpsimp wp: guarded_switch_to_lift switch_to_thread_valid_sched
                             set_scheduler_action_rct_valid_sched_ct
                             stt_activatable[simplified ct_in_state_def]
                             hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                             switch_to_thread_sched_act_is_cur
                             switch_to_thread_ct_not_in_release_q switch_to_thread_invs)+
           apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
           apply wpsimp+
          apply (wpsimp wp: guarded_switch_to_lift switch_to_thread_valid_sched
                            set_scheduler_action_rct_valid_sched_ct
                            stt_activatable[simplified ct_in_state_def]
                            hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                            switch_to_thread_sched_act_is_cur
                            switch_to_thread_ct_not_in_release_q switch_to_thread_invs)+
      (* discard result of fastfail calculation *)
       apply (wpsimp wp: hoare_drop_imp)+
   apply (clarsimp simp: not_cur_thread_def valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                         switch_in_cur_domain_def active_sc_tcb_at_defs valid_blocked_def
                         ct_in_q_def in_release_queue_def not_in_release_q_def cur_tcb_def
                         is_tcb get_tcb_rev is_schedulable_bool_def valid_blocked_except_def
                  split: option.splits)
    (* choose new thread *)
  apply (case_tac ct_schedulable; clarsimp)
   apply (wpsimp wp: schedule_choose_new_thread_valid_sched
                     schedule_choose_new_thread_ct_not_in_release_q
                     schedule_choose_new_thread_ct_not_queued
                     sc_and_timer_valid_sched)
     apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
     apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
    apply (rule hoare_vcg_conj_lift)
     apply (rule_tac Q="\<lambda>_ s. (\<exists>d p. cur_thread s \<in> set (ready_queues s d p))" in hoare_strengthen_post)
      apply (rule enqueue_thread_queued_ct)
     apply (clarsimp simp: ct_in_q_def)
    apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
   apply (clarsimp simp: valid_sched_def active_sc_tcb_at_defs valid_blocked_def get_tcb_rev
                          valid_blocked_except_def ct_in_state_def runnable_eq_active is_schedulable_bool_def not_in_release_q_def
                  split: option.splits)
  apply (wpsimp wp: schedule_choose_new_thread_valid_sched
                    schedule_choose_new_thread_ct_not_in_release_q
                    schedule_choose_new_thread_ct_not_queued
                    sc_and_timer_valid_sched)
   apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and> valid_machine_time s" in hoare_strengthen_post[rotated], simp)
   apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
  by (clarsimp simp: valid_sched_def ct_in_q_def not_in_release_q_def in_release_queue_def
                     is_schedulable_bool_def active_sc_tcb_at_defs cur_tcb_def is_tcb get_tcb_rev
              split: option.splits)

crunches awaken
  for ct_active[wp]: ct_active
  and ct_idle[wp]: ct_idle
  and ct_active_or_idle[wp]: "ct_active or ct_idle"
    (wp: crunch_wps hoare_vcg_disj_lift simp: crunch_simps pred_disj_def)

lemma refill_ready_tcb_sp:
  "\<lbrace> P \<rbrace> refill_ready_tcb t
      \<lbrace> \<lambda>rv s. P s \<and> (rv \<longrightarrow> budget_ready t s \<and> budget_sufficient t s) \<rbrace>"
  apply (clarsimp simp: refill_ready_tcb_def refill_ready_def refill_sufficient_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp simp: assert_opt_def)
  apply (rename_tac scp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ get_refills_sp])
  apply (simp add: valid_def return_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
  by (intro conjI; rule_tac x=scp in exI, clarsimp)

crunches possible_switch_to
  for release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
  and ct_release_queue[wp]: "\<lambda>s::det_state. P (cur_thread s) (release_queue s)"
  and budget_ready_ct'[wp]: "\<lambda>s::det_state. P (budget_ready (cur_thread s) s)"
  and budget_ready_ct'[wp]: "\<lambda>s::det_state. P (budget_ready (cur_thread s) s)"
  and budget_sufficient_ct'[wp]: "\<lambda>s::det_state. P (budget_sufficient (cur_thread s) s)"
    (simp: crunch_simps wp: crunch_wps)

crunches awaken
  for budget_ready_ct'[wp]: "\<lambda>s::det_state. P (budget_ready (cur_thread s) s)"
  and budget_sufficient_ct'[wp]: "\<lambda>s::det_state. P (budget_sufficient (cur_thread s) s)"
  and sc_at_period[wp]: "sc_at_period P p::det_state \<Rightarrow> _"
  and sc_at_period_cur[wp]: "\<lambda>s::det_state. sc_at_period P (cur_sc s) s"
  and valid_machine_time[wp]: "valid_machine_time::det_state \<Rightarrow> _"
    (simp: crunch_simps wp: crunch_wps)

lemma possible_switch_to_in_release_q_not_ready:
  "\<lbrace> \<lambda>s::det_state. \<forall>t. in_release_q t s \<longrightarrow> \<not> budget_ready t s \<rbrace>
    possible_switch_to thread
    \<lbrace>\<lambda>rv s. \<forall>t. in_release_q t s \<longrightarrow> \<not> budget_ready t s\<rbrace>"
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift simp: in_release_q_def)

(* FIXME move *)
lemma valid_release_q_sorted: "valid_release_q s \<Longrightarrow> sorted_release_q s"
  by (clarsimp simp: valid_release_q_def)

lemma dropWhile_release_queue:
"\<lbrakk> valid_release_q s; \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s;
  t \<in> set (dropWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s))
                      (release_queue s))\<rbrakk> \<Longrightarrow> \<not>budget_ready t s"
  apply (frule set_dropWhileD)
  apply (frule (1) valid_release_q_active_sc)
  apply (frule valid_release_q_sorted)
  apply (subgoal_tac
      "(dropWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s))
                (release_queue s)) =
           (dropWhile (\<lambda>t. tcb_ready_time t s \<le> (cur_time s) + kernelWCET_ticks)
                (release_queue s))")
   prefer 2
   apply (rule dropWhile_cong, clarsimp)
   apply (clarsimp simp:  simp: valid_release_q_def)
   apply (drule_tac x=x in bspec, simp)
   apply (drule_tac x=x in spec, clarsimp simp: in_release_q_def)
   apply (subst refill_ready_tcb_simp2, simp+)
  apply (thin_tac "(dropWhile _ _)=  _")
  apply (frule sorted_wrt_dropWhile_mono[rotated, where f="\<lambda>t. tcb_ready_time t s"])
  by (auto simp: sorted_release_q_def tcb_ready_time_def get_tcb_rev refill_prop_defs active_sc_tcb_at_defs split: option.splits)

lemma awaken_wp: (* release_queue is ordered by r_time *)
  "\<lbrace> valid_release_q
 and (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s)\<rbrace>
    awaken
    \<lbrace>\<lambda>rv s::det_state.
        \<forall>t. in_release_q t s \<longrightarrow> \<not> budget_ready t s\<rbrace>"
  apply (clarsimp simp: awaken_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sp])
  apply (wpsimp wp: mapM_x_wp_inv possible_switch_to_in_release_q_not_ready simp: Ball_def)
  apply (clarsimp simp: dropWhile_eq_drop[symmetric])
  by (frule_tac t=t in dropWhile_release_queue; clarsimp simp: in_release_q_def)

lemma awaken_cur_thread_in_rlq:
  "\<lbrace> \<lambda>s::det_state. cur_tcb s \<and> (\<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s)
 \<and> active_sc_tcb_at (cur_thread s) s \<and>
 budget_sufficient (cur_thread s) s \<and> valid_release_q s \<rbrace>
      awaken
    \<lbrace>\<lambda>rv s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: awaken_def)
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift)
  by (fastforce simp: dropWhile_eq_drop[symmetric] in_release_q_def dest!: dropWhile_release_queue)

lemma awaken_cur_thread_not_in_rlq:
  "\<lbrace> \<lambda>s::det_state. cur_tcb s \<and> valid_release_q s
       \<and> budget_sufficient (cur_thread s) s \<and>
        (not_in_release_q (cur_thread s) s \<longrightarrow>
        budget_ready (cur_thread s) s) \<rbrace>
      awaken
    \<lbrace>\<lambda>rv s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: awaken_def not_in_release_q_def)
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift hoare_vcg_conj_lift)
  apply (clarsimp simp: dropWhile_eq_drop[symmetric])
  apply (drule (1) dropWhile_dropped_P[rotated])
  apply (clarsimp simp: cur_tcb_def obj_at_def pred_tcb_at_def is_tcb is_sc_obj_def)
  apply (rename_tac ko tcb n, case_tac ko; clarsimp)
  apply (rename_tac sc n)
  apply (fastforce simp: fun_of_m_def is_refill_ready_def is_refill_sufficient_def obj_at_def)
  done

lemma awaken_cur_thread_not_in_rlq2:
  "\<lbrace> \<lambda>s::det_state. cur_tcb s \<and> valid_release_q s
       \<and> budget_sufficient (cur_thread s) s \<and>
        (in_release_q (cur_thread s) s \<longrightarrow>
        \<not>budget_ready (cur_thread s) s) \<and>
        (not_in_release_q (cur_thread s) s \<longrightarrow>
        budget_ready (cur_thread s) s) \<rbrace>
      awaken
    \<lbrace>\<lambda>rv s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: awaken_def not_in_release_q_def)
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift hoare_vcg_conj_lift)
  apply (clarsimp simp: dropWhile_eq_drop[symmetric])
  apply (drule (1) dropWhile_dropped_P[rotated])
  apply (clarsimp simp: cur_tcb_def obj_at_def pred_tcb_at_def is_tcb is_sc_obj_def)
  apply (rename_tac ko tcb n, case_tac ko; clarsimp)
  apply (rename_tac sc n)
  apply (fastforce simp: fun_of_m_def is_refill_ready_def is_refill_sufficient_def obj_at_def in_release_q_def)
  done

lemma possible_switch_to_not_queued:
  "\<lbrace>not_queued t and K (t \<noteq> thread) and scheduler_act_not t\<rbrace>
     possible_switch_to thread \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  by (wpsimp wp: tcb_sched_enqueue_not_queued hoare_drop_imp reschedule_required_not_queued)

lemma possible_switch_to_ct_not_queued':
  "\<lbrace>ct_not_queued and (\<lambda>s. cur_thread s \<noteq> thread) and scheduler_act_sane\<rbrace>
     possible_switch_to thread \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  apply (wpsimp wp: hoare_drop_imp reschedule_required_ct_not_queued)
  apply (wpsimp wp: tcb_sched_enqueue_not_queued | wps)+
  by (wpsimp wp: hoare_drop_imp) clarsimp

lemma possible_switch_to_scheduler_act_sane'':
  "\<lbrace>scheduler_act_sane and (\<lambda>s. cur_thread s \<noteq> thread)\<rbrace>
     possible_switch_to thread \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  by (wpsimp wp: tcb_sched_action_scheduler_action hoare_drop_imp simp: set_scheduler_action_def)
     (clarsimp simp: scheduler_act_sane_def)

lemma awaken_ct_not_queued_helper:
  "\<lbrace>ct_not_queued and (\<lambda>s. cur_thread s \<notin> set queue) and scheduler_act_sane\<rbrace>
     mapM_x (\<lambda>t. do y <- possible_switch_to t;
               modify (reprogram_timer_update (\<lambda>_. True))
             od) queue
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (induction queue, wpsimp simp: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
  by (wpsimp wp: possible_switch_to_ct_not_queued possible_switch_to_scheduler_act_sane'')

lemma awaken_ct_not_queued:
  "\<lbrace>ct_not_queued and scheduler_act_sane and
        (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
        (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> (\<not> budget_ready (cur_thread s) s))\<rbrace>
     awaken \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: awaken_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_ct_not_queued_helper)
  apply (drule set_takeWhileD)
  apply (drule_tac x="cur_thread s" in spec, clarsimp simp: in_release_q_def)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs )
  apply (simp add: refill_ready_tcb_simp3[where t="cur_thread s" for s])
  apply (clarsimp simp: tcb_ready_time_def get_tcb_rev split: option.splits)
  done

crunches possible_switch_to
  for cur_sc_in_release_q_imp_zero_consumed[wp]: cur_sc_in_release_q_imp_zero_consumed
  and it_release_queue[wp]: "\<lambda>s::det_state. P (idle_thread s) (release_queue s)"
    (wp: crunch_wps simp: crunch_simps)

crunches awaken
  for sc_is_round_robin[wp]: "\<lambda>s::det_state. P (sc_is_round_robin p s)"
  and sc_is_round_robin_cur[wp]: "\<lambda>s::det_state. P (sc_is_round_robin (cur_sc s) s)"
    (wp: crunch_wps simp: crunch_simps)

lemma awaken_ct_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "\<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>
     awaken \<lbrace>\<lambda>_. cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  apply (wpsimp simp: awaken_def wp: mapM_x_wp')
  apply (drule_tac x=t in spec, clarsimp simp: not_in_release_q_def)
  apply (clarsimp simp: in_queue_2_def dropWhile_eq_drop[symmetric] pred_tcb_at_def obj_at_def)
  apply (drule set_dropWhileD, clarsimp)
  done

lemma awaken_it_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s::det_state. not_in_release_q (idle_thread s) s\<rbrace>
     awaken \<lbrace>\<lambda>_. \<lambda>s::det_state. not_in_release_q (idle_thread s) s\<rbrace>"
  apply (wpsimp simp: awaken_def wp: mapM_x_wp')
  apply (clarsimp simp: not_in_release_q_def dropWhile_eq_drop[symmetric])
  by (drule set_dropWhileD, clarsimp)

crunches possible_switch_to
  for cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: crunch_wps)

crunches possible_switch_to
  for in_release_q[wp]: "\<lambda>s. Q (in_release_q t s)"
  and consumed_time[wp]: "\<lambda>s. Q (consumed_time s)"
  (wp: crunch_wps)

(* FIXME move *)
lemma sorted_wrt_takeWhile_mono:
  "\<lbrakk>sorted_wrt (\<lambda>x y. f x \<le> f y) ls;
    t \<in> set (takeWhile P ls); \<forall>x y. f x \<le> f y \<longrightarrow> P y \<longrightarrow> P x\<rbrakk> \<Longrightarrow> P t "
  by (induction ls; auto split: if_split_asm)

lemma takeWhile_release_queue:
  "\<lbrakk> valid_release_q s; \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s;
     t \<in> set (takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) (release_queue s))\<rbrakk>
             \<Longrightarrow> budget_ready t s"
  apply (frule set_takeWhileD)
  apply clarsimp
  apply (frule (1) valid_release_q_active_sc)
  apply (frule valid_release_q_sorted)
  apply (subgoal_tac
      "(takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s))
                (release_queue s)) =
           (takeWhile (\<lambda>t. tcb_ready_time t s \<le> (cur_time s) + kernelWCET_ticks)
                (release_queue s))")
   prefer 2
   apply (rule takeWhile_cong, clarsimp)
   apply (clarsimp simp:  simp: valid_release_q_def)
   apply (drule_tac x=x in bspec, simp)
   apply (drule_tac x=x in spec, clarsimp simp: in_release_q_def)
   apply (subst refill_ready_tcb_simp2, simp+)
  apply (thin_tac "(takeWhile _ _)=  _")
  apply (frule sorted_wrt_takeWhile_mono[rotated, where f="\<lambda>t. tcb_ready_time t s"])
    apply fastforce
   apply (fastforce simp: sorted_release_q_def)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  apply (case_tac y; simp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb is_refill_ready_def tcb_ready_time_def get_tcb_def is_sc_obj)

lemma awaken_ct_nrq_wbr:
  "\<lbrace>(\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s) and
    (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s) and
    valid_release_q and
    (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s)\<rbrace>
    awaken
   \<lbrace>\<lambda>_ s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s\<rbrace>"
  unfolding awaken_def
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift')
         apply (rule hoare_lift_Pf[where f=cur_thread])
          apply (wpsimp simp: not_not_in_eq_in in_release_queue_in_release_q)+
        apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift')+
        apply (rule hoare_lift_Pf[where f=cur_thread])
         apply (rule hoare_lift_Pf[where f=consumed_time])
          apply wpsimp+
  apply (clarsimp simp: not_not_in_eq_in in_release_queue_in_release_q in_release_q_def not_in_release_q_def)
  apply (rule FalseE, subst (asm) (2) not_def, erule mp)
  apply (erule distinct_not_in_takeWhile[rotated])
   apply (clarsimp simp: )
   apply (subst (asm) not_def, erule mp)
   apply (erule takeWhile_release_queue[rotated, rotated])
    apply (clarsimp simp: in_release_q_def)+
  done

(* ct_schedulable \<longrightarrow> ready & sufficient *)
lemma schedule_valid_sched:
  "\<lbrace> valid_release_q and ct_active and
    (\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s) and
    (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
    (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s) and
    (\<lambda>s. budget_sufficient (cur_thread s) s) and
    (\<lambda>s. is_schedulable_bool (cur_thread s) (in_release_q (cur_thread s) s) s \<longrightarrow>
              budget_ready (cur_thread s) s \<and> budget_sufficient (cur_thread s) s) and
    \<comment> \<open>(\<lambda>s. cur_thread s \<notin> set (release_queue s) \<longrightarrow> budget_ready (cur_thread s) s) and\<close>
   (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and (\<lambda>s.  \<not> sc_is_round_robin (cur_sc s) s)
     and cur_tcb and valid_sched and valid_idle and scheduler_act_sane and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed and valid_machine_time and invs\<rbrace>
   schedule
  \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_def
  apply (wpsimp wp: schedule_valid_sched_helper awaken_valid_sched
                    awaken_cur_thread_not_in_rlq awaken_ct_not_queued awaken_ct_nrq_wbr
                    hoare_vcg_ball_lift hoare_vcg_conj_lift awaken_wp awaken_cur_thread_in_rlq
              simp: cur_tcb_def is_tcb active_sc_tcb_at_defs get_tcb_rev is_schedulable_bool_def
             split: option.splits)
  by (clarsimp dest!: valid_sched_valid_release_q
                simp: not_in_release_q_def valid_release_q_def in_release_q_def active_sc_tcb_at_defs
                      ct_in_state_def runnable_eq)

crunches cancel_ipc
for not_cur_thread[wp]: "not_cur_thread thread"
  (wp: hoare_drop_imps select_wp mapM_x_wp simp: unless_def if_fun_split)

lemma cancel_ipc_sc_tcb_sc_at_eq[wp]:
  "cancel_ipc thread \<lbrace>sc_tcb_sc_at ((=) tcb_opt) x\<rbrace>"
  unfolding cancel_ipc_def
  by (wpsimp simp: blocked_cancel_ipc_def get_blocking_object_def
                   reply_remove_tcb_def cancel_signal_def
               wp: get_simple_ko_wp get_ep_queue_wp hoare_vcg_all_lift hoare_drop_imps
                   update_sched_context_sc_tcb_sc_at)

lemma cancel_ipc_bound_sc_tcb_at[wp]:
  "cancel_ipc thread \<lbrace>bound_sc_tcb_at P thread\<rbrace>"
  unfolding cancel_ipc_def
  apply (wpsimp simp: reply_remove_tcb_def
                  wp: gts_wp thread_set_wp get_sk_obj_ref_wp)
  apply (clarsimp dest!: get_tcb_SomeD
                   simp: pred_tcb_at_def obj_at_def)
  done

lemma restart_valid_sched:
  "\<lbrace>valid_sched
    and (\<lambda>s. thread \<noteq> idle_thread s)
    and valid_objs
    and scheduler_act_not thread
    and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   restart thread
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding restart_def
  apply (wpsimp wp: test_possible_switch_to_valid_sched)
       apply (rule_tac Q="\<lambda>r s. valid_sched_except_blocked s
                                \<and> valid_blocked_except_set {thread} s
                                \<and> thread \<noteq> idle_thread s
                                \<and> (st_tcb_at runnable thread s \<and> active_sc_tcb_at thread s \<and>
                                   not_in_release_q thread s \<longrightarrow>
                                   budget_ready thread s \<and> budget_sufficient thread s)"
                       in hoare_strengthen_post[rotated])
        apply (intro allI conjI;
               intro impI;
               clarsimp simp: valid_sched_def dest!: is_schedulable_opt_Some)
        apply (fastforce elim!: valid_blocked_divided2
                          simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def)
       apply (wpsimp wp: sched_context_resume_valid_sched_except_blocked
                         sched_context_resume_valid_blocked_except_set
                         sched_context_resume_cond_budget_ready_sufficient)
      apply wpsimp
      apply (rule_tac Q="\<lambda>r. (valid_sched_except_blocked and
                             valid_blocked_except_set {thread}) and
                             scheduler_act_not thread and
                             not_queued thread and
                             (\<lambda>s. thread \<noteq> idle_thread s) and
                             (\<lambda>s. \<forall>sc_ptr. sc_opt = (Some sc_ptr)
                                           \<longrightarrow> sc_tcb_sc_at ((=) (Some thread)) sc_ptr s) and
                             bound_sc_tcb_at (\<lambda>a. a = sc_opt) thread"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp simp: sc_at_pred_n_eq_commute )
       apply (fastforce simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift set_thread_state_break_valid_sched)
     apply (clarsimp)
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift cancel_ipc_valid_sched)
    apply (wpsimp simp: get_tcb_obj_ref_def  wp: thread_get_wp )
   apply (wpsimp wp: gts_wp )
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac x=tcb in exI; clarsimp)
  apply (intro conjI)
    apply (fastforce dest: valid_sched_not_runnable_not_inq simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def
                         pred_tcb_at_def obj_at_def)
  apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[where t=thread, symmetric];
         simp?;
         fastforce simp: pred_tcb_at_def obj_at_def)
  done

end

lemma bind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> bind_notification param_a param_b \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: bind_notification_def update_sk_obj_ref_def)
  apply (wpsimp simp: set_object_def set_simple_ko_def
          wp: get_simple_ko_wp hoare_drop_imp set_bound_notification_valid_sched)
  done

lemma suspend_it_det_ext[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> suspend param_a \<lbrace>\<lambda>_ s::det_ext state. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: suspend_def wp: hoare_drop_imps)


context DetSchedSchedule_AI begin

lemma invoke_tcb_valid_sched:
  "\<lbrace>invs
    and valid_sched and ct_active and ct_ARS
    and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases ti, simp_all only:)
          apply (wpsimp wp: restart_valid_sched reschedule_valid_sched_const)
              apply (intro impI conjI)
               apply wpsimp+
               apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated])
                apply fastforce
               apply (wpsimp wp: suspend_invs)+
          apply (clarsimp simp: invs_valid_objs invs_valid_global_refs idle_no_ex_cap)
         apply (wpsimp wp: suspend_valid_sched;
                clarsimp simp: invs_valid_objs invs_valid_global_refs)
        apply ((wp mapM_x_wp suspend_valid_sched restart_valid_sched reschedule_valid_sched_const
               | simp
               | rule subset_refl
               | intro impI conjI)+)[1]
          apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated])
           apply fastforce
          apply (wpsimp wp: suspend_invs suspend_valid_sched)+
        apply (fastforce simp: invs_def valid_state_def valid_idle_def dest!: idle_no_ex_cap)
       apply (wp tcc_valid_sched)
       apply (rename_tac sc_opt_opt s, case_tac sc_opt_opt; simp)
      apply (wp tcs_valid_sched)
      apply (rename_tac sc_opt_opt s, case_tac sc_opt_opt; simp)
     apply (rename_tac sc_opt, case_tac sc_opt; simp)
     apply (wpsimp wp: suspend_valid_sched ;
            clarsimp simp: invs_valid_objs invs_valid_global_refs)
    apply (wpsimp wp: mapM_x_wp suspend_valid_sched restart_valid_sched;
           intro conjI;
           clarsimp simp: invs_valid_objs invs_valid_global_refs idle_no_ex_cap)
   apply (rename_tac option, case_tac option; wpsimp)
  apply (wpsimp wp: reschedule_valid_sched_const)
  done

end

crunch valid_sched[wp]: store_word_offs "valid_sched::det_state \<Rightarrow> _"

crunch exst[wp]: set_mrs, as_user "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

crunch ct_not_in_q[wp]: as_user ct_not_in_q
  (wp: ct_not_in_q_lift)

(* here *)
lemmas gts_drop_imp = hoare_drop_imp[where f="get_thread_state p" for p]

lemma as_user_valid_blocked_except_set[wp]:
 "\<lbrace>valid_blocked_except_set S\<rbrace> as_user param_a param_b \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_blocked_except_lift)

crunch not_cur_thread[wp]: cap_insert, set_extra_badge "not_cur_thread t"
  (wp: hoare_drop_imps dxo_wp_weak)

lemma transfer_caps_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+


crunch not_cur_thread[wp]: as_user "not_cur_thread t"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

crunch (in DetSchedSchedule_AI) not_cur_thread[wp] : do_ipc_transfer "not_cur_thread t::det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

lemma postpone_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q \<rbrace>
     postpone sc_ptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp:get_sc_obj_ref_wp)

lemma sched_context_resume_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q \<rbrace>
     sched_context_resume sc_opt
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: thread_get_wp is_schedulable_wp refill_sufficient_wp refill_ready_wp)
     (fastforce simp: obj_at_def is_schedulable_opt_def is_tcb
               split: option.splits dest!: get_tcb_SomeD)

lemma is_etcb_at_etcbs_of_tcb_at:
  "is_etcb_at' x (etcbs_of s) = tcb_at x s"
  apply (clarsimp simp: is_etcb_at'_def etcbs_of'_def tcb_at_def iff_conv_conj_imp get_tcb_def
                  dest!: get_tcb_SomeD split: option.splits | safe)+
  apply (case_tac x2; simp)+
  done

(* FIXME: move *)
lemma hoare_vcg_imp_lift'':
  "\<lbrakk> \<lbrace>\<lambda>s. \<not> P' s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  by (wp hoare_vcg_disj_lift)

lemma refill_unblock_check_valid_release_q':
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (clarsimp simp: refill_unblock_check_def)
     (wpsimp wp: get_refills_wp set_refills_valid_release_q_not_in_release_q
                 is_round_robin_wp refill_ready_wp)

lemma maybe_donate_sc_ct_not_in_q:
  "\<lbrace> ct_not_in_q and (\<lambda>s. tcb_ptr \<noteq> cur_thread s)\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

crunches sched_context_donate
  for machine_state[wp]: "(\<lambda>s. P (machine_state s)) :: det_state \<Rightarrow> _"
  and cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: det_state \<Rightarrow> _"
  and valid_machine_time[wp]: "valid_machine_time::det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma maybe_donate_sc_valid_ready_qs:
  "\<lbrace> valid_machine_time and valid_ready_qs and scheduler_act_not tcb_ptr and not_queued tcb_ptr \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_valid_ready_qs refill_unblock_check_valid_ready_qs
      hoare_vcg_if_lift2 maybeM_wp valid_machine_time_lift simp: get_sc_obj_ref_def obj_at_def)
   apply wpsimp
  done

lemma refill_unblock_check_ko_at_SchedContext:
  "\<lbrace>\<lambda>s. P (sc_tcb_sc_at ((=) (Some ya)) scp s)\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_tcb_sc_at ((=) (Some ya)) scp s)\<rbrace>"
   unfolding refill_unblock_check_def
  by (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
     (clarsimp simp: sc_at_pred_n_def obj_at_def)

lemma maybe_donate_sc_valid_release_q_helper:
  "\<lbrace>not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr and sc_tcb_sc_at ((=) None) scp\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) scp s \<longrightarrow>
               st_tcb_at runnable x s \<and> not_in_release_q x s \<and> bound_sc_tcb_at ((=) (Some scp)) x s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
  apply (rule hoare_pre_cont)
  apply (wpsimp)+
  apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply (safe)
    apply clarsimp
    apply (clarsimp simp: st_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

crunches test_reschedule
  for not_in_release_q'[wp]: "not_in_release_q t"

lemma sched_context_donate_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>y s. not_in_release_q t s\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def
                  wp: set_object_wp update_sched_context_wp hoare_drop_imp
                      tcb_release_remove_not_in_release_q' get_sc_obj_ref_wp)

lemma sched_context_donate_wp:
  "\<lbrace>\<top>\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>y. sc_tcb_sc_at ((=) (Some tcb_ptr)) scp and
                  bound_sc_tcb_at ((=) (Some scp)) tcb_ptr\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: ssc_bound_tcb_at' sc_tcb_update_sc_tcb_sc_at)


lemma maybe_donate_sc_valid_release_q_helper':
  "\<lbrace>valid_release_q and bound_sc_tcb_at ((=) None) tcb_ptr
       and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s::det_state. \<forall>t\<in>set (release_queue s).
                bound_sc_tcb_at (\<lambda>p. p \<noteq> Some scp) t s\<rbrace>"
  apply (rule_tac Q="valid_release_q and not_in_release_q tcb_ptr and valid_objs
                      and (\<lambda>s. sym_refs (state_refs_of s)) and bound_sc_tcb_at ((=) None) tcb_ptr"
           in hoare_weaken_pre[rotated])
   apply (clarsimp dest!: valid_and_no_sc_imp_not_in_release_q[rotated])
  apply (rule_tac Q="\<lambda>_ . sc_tcb_sc_at ((=) (Some tcb_ptr)) scp
                    and bound_sc_tcb_at ((=) (Some scp)) tcb_ptr and not_in_release_q tcb_ptr
                    and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs and valid_release_q"
           in hoare_strengthen_post)
   apply (wpsimp wp: sched_context_donate_wp sched_context_donate_not_in_release_q
      sched_context_donate_valid_release_q sched_context_donate_sym_refs)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_release_q_def)
  apply (drule_tac x=t in bspec, simp)
  apply (clarsimp simp: not_in_release_q_def sc_tcb_sc_at_def active_sc_tcb_at_defs split: option.splits)
  apply (frule_tac tp=tcb_ptr in ARM.sym_ref_tcb_sc, simp+)
  apply (drule_tac tp=t in ARM.sym_ref_tcb_sc, simp+)
  done

crunches test_reschedule
  for sc_not_in_release_q[wp]: "sc_not_in_release_q t"
  (wp: crunch_wps simp: crunch_simps)

lemma tcb_release_remove_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q sc_ptr\<rbrace>
    tcb_release_remove tptr
   \<lbrace>\<lambda>rv. sc_not_in_release_q sc_ptr\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  by (clarsimp simp: pred_tcb_at_def obj_at_def tcb_sched_dequeue_def not_in_release_q_def)

lemma set_sc_tcb_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q scp\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. sc_not_in_release_q scp\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def split: if_splits)

lemma sched_context_donate_sc_not_in_release_q:
  "\<lbrace>sc_not_in_release_q sc_ptr and not_in_release_q tptr\<rbrace>
    sched_context_donate scp tptr
   \<lbrace>\<lambda>rv. sc_not_in_release_q sc_ptr::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  by (wp get_sc_obj_ref_wp)
     (clarsimp simp: pred_tcb_at_def obj_at_def not_in_release_q_def)

lemma maybe_donate_sc_valid_release_q:
  "\<lbrace> valid_release_q and not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr
           and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (clarsimp simp: maybeM_def)
   apply (rename_tac scp; case_tac scp; clarsimp)
    apply wpsimp
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (rename_tac sctcb; case_tac sctcb; clarsimp)
    apply (wpsimp wp: sched_context_resume_valid_release_q refill_unblock_check_valid_release_q
                      refill_unblock_check_sc_not_in_release_q sched_context_donate_valid_release_q
                      sched_context_donate_sc_not_in_release_q)
    apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def)
    apply (drule (2) bound_sc_tcb_bound_sc_at)
     apply (fastforce simp: pred_tcb_at_def obj_at_def sc_tcb_sc_at_def)
    apply fastforce
  by (wpsimp wp: sched_context_donate_valid_release_q maybe_donate_sc_valid_release_q_helper')+

lemma maybe_donate_sc_valid_sched_action_helper:
  "\<lbrace>scheduler_act_not tcb_ptr and sc_tcb_sc_at ((=) None) scp\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) scp s \<longrightarrow> scheduler_act_not x s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
        apply (rule hoare_pre_cont)
       apply (wpsimp)+
   apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  done

lemma maybe_donate_sc_valid_sched_action:
  "\<lbrace> valid_sched_action and scheduler_act_not tcb_ptr and valid_machine_time\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_valid_sched_action)
      apply (wpsimp wp: refill_unblock_check_valid_sched_action hoare_vcg_all_lift
                        hoare_vcg_imp_lift'' refill_unblock_check_ko_at_SchedContext)
     apply (wpsimp wp: sched_context_donate_valid_sched_action
                       maybe_donate_sc_valid_sched_action_helper)
    apply (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)
   apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  apply wpsimp
  done

lemma postpone_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     postpone t
   \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: get_sc_obj_ref_wp)

lemma sched_context_resume_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     sched_context_resume sc_opt
   \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_ct_in_cur_domain is_schedulable_wp refill_ready_wp refill_sufficient_wp
           simp: thread_get_def)

lemma maybe_donate_sc_ct_in_cur_domain:
  "\<lbrace> ct_in_cur_domain \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: sched_context_resume_ct_in_cur_domain refill_unblock_check_ct_in_cur_domain
                    get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma not_queued_refill_unblock_check:
  "\<lbrace>\<lambda>s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_donate_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set {tcb_ptr} and sc_tcb_sc_at ((=) None) sc_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>y. valid_blocked_except_set {tcb_ptr}\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
        apply (rule hoare_pre_cont)
       apply (wpsimp)+
   apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply (safe)
   apply clarsimp
  apply (clarsimp simp: valid_blocked_except_set_2_def
                 dest!: get_tcb_SomeD)
  apply (subgoal_tac "st_tcb_at ((=) st) t s")
   apply (subgoal_tac "active_sc_tcb_at t s")
    apply fastforce
   apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def obj_at_kh_def
                         active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_def test_sc_refill_max_kh_def
                         test_sc_refill_max_def
                   split: if_splits )
  apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
  apply (case_tac "t = sc_ptr"; clarsimp)
  done

lemma not_queued_sched_context_donate:
  "\<lbrace>not_queued tcb_ptr and scheduler_act_not tcb_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  apply (wpsimp wp: get_sched_context_wp hoare_vcg_all_lift set_object_wp get_object_wp)
      apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
     apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_wp)
    apply (rule_tac Q="\<lambda>r. not_queued tcb_ptr" in hoare_strengthen_post)
     prefer 2
     apply (clarsimp simp: not_queued_def sc_tcb_sc_at_def obj_at_def dest!: get_tcb_SomeD)
    apply (wpsimp wp: tcb_dequeue_not_queued_gen simp: get_sc_obj_ref_def)+
  done

lemma maybe_donate_sc_valid_blocked_except_set:
  "\<lbrace> valid_blocked_except_set {tcb_ptr} and not_queued tcb_ptr and scheduler_act_not tcb_ptr\<rbrace>
      maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_blocked_except_set {tcb_ptr} :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (wpsimp wp: sched_context_resume_valid_blocked_except_set
                    refill_unblock_check_valid_blocked_except_set
                    not_queued_refill_unblock_check not_queued_sched_context_donate
                    sched_context_donate_valid_blocked_except_set
                    get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

crunches maybe_donate_sc
for not_cur_thread[wp]: "not_cur_thread t"
and etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: hoare_drop_imp crunch_wps ignore: set_tcb_obj_ref simp: crunch_simps)

(*
context DetSchedSchedule_AI begin
lemma update_waiting_ntfn_valid_sched:
  "\<lbrace> \<lambda>s. valid_sched s \<and> scheduler_act_not (hd queue) s \<and>
     hd queue \<noteq> idle_thread s \<and>
     (scheduler_action s = resume_cur_thread \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace>
       update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (wpsimp wp: set_thread_state_runnable_valid_sched sts_st_tcb_at')
  apply (wpsimp wp: set_thread_state_runnable_valid_sched sts_st_tcb_at'
maybe_donate_sc_valid_sched maybe_donate_sc_active_sc_tcb_at_eq)
  apply (wp sts_st_tcb_at' possible_switch_to_valid_sched_weak
            set_thread_state_runnable_valid_sched
            set_thread_state_runnable_valid_ready_qs
            set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except
            | clarsimp)+
  apply (clarsimp simp: valid_sched_def not_cur_thread_def ct_not_in_q_def)
  apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
apply (wpsimp wp: assert_wp)

apply (clarsimp simp: pred_tcb_at_def ntfn_sc_ntfn_at_def obj_at_def partial_inv_def the_equality, intro conjI allI impI)


end*)

crunch valid_sched[wp]: dec_domain_time valid_sched

lemmas bound_sc_tcb_at_def = pred_tcb_at_def

lemma tcb_sched_enqueue_queued[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_enqueue tcb_ptr \<lbrace>\<lambda>rv s. (\<not> not_queued tcb_ptr s)\<rbrace>"
  unfolding tcb_sched_action_def tcb_sched_enqueue_def
  apply wpsimp
  apply (clarsimp simp: not_queued_def obj_at_def)
  apply fastforce
  done

lemma cancel_badged_sends_valid_sched_helper_valid_ep_thread_simple:
   "\<lbrace>valid_ep_thread_simple t'\<rbrace>
    do st \<leftarrow> get_thread_state t;
             if blocking_ipc_badge st = badge
             then do _ \<leftarrow> restart_thread_if_no_fault t;
                          return False
             od
             else return True
    od
    \<lbrace>\<lambda>rv. valid_ep_thread_simple t' :: det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp hoare_drop_imps)

lemma cancel_badged_sends_valid_sched_helper_st_tcb_at:
   "\<lbrace>st_tcb_at (not runnable) t' and K (t' \<noteq> t)\<rbrace>
    do st \<leftarrow> get_thread_state t;
             if blocking_ipc_badge st = badge
             then do _ \<leftarrow> restart_thread_if_no_fault t;
                          return False
             od
             else return True
    od
    \<lbrace>\<lambda>rv. st_tcb_at (not runnable) t'\<rbrace>"
  by (wpsimp wp: restart_thread_if_no_fault_other reply_unlink_tcb_st_tcb_at gts_wp)

lemma cancel_badged_sends_filterM_valid_sched:
   "\<lbrace>(\<lambda>s. \<forall>t\<in>set xs. valid_ep_thread_simple t s \<and> st_tcb_at (not runnable) t s)
     and valid_sched and K (distinct xs)\<rbrace>
    filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                    if blocking_ipc_badge st = badge
                    then do _ \<leftarrow> restart_thread_if_no_fault t;
                            return False
                    od
                    else return True
                 od) xs
    \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_filterM_scheme)
    by (wpsimp wp: cancel_badged_sends_valid_sched_helper_valid_ep_thread_simple
                   cancel_badged_sends_valid_sched_helper_st_tcb_at
                   restart_thread_if_no_fault_valid_sched gts_wp)+

lemma cancel_badged_sends_valid_sched:
  "\<lbrace>valid_objs and valid_sched and valid_ep_q and simple_sched_action
    and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_badged_sends epptr badge
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp;
          wpsimp wp: cancel_badged_sends_filterM_valid_sched hoare_vcg_ball_lift
                     reschedule_valid_sched_const)
  by (auto simp: obj_at_def is_ep valid_objs_ko_at valid_obj_def valid_ep_def
                 ep_queued_st_tcb_at pred_neg_def
          dest!: valid_ep_q_imp_valid_ep_thread_simple)

context DetSchedSchedule_AI begin

lemma cap_revoke_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action and invs\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule validE_valid, rule cap_revoke_preservation)
    apply (wpsimp wp: preemption_point_inv')+
  done

lemma cap_revoke_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wp cap_revoke_preservation preemption_point_inv' | fastforce)+

end

lemma thread_set_state_eq_valid_ready_qs:
  "\<lbrakk> \<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x;
     \<And>x. tcb_sched_context (f x) = tcb_sched_context x \<rbrakk> \<Longrightarrow>
   \<lbrace>valid_ready_qs and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wpsimp
  apply (clarsimp simp: valid_ready_qs_def etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  apply (clarsimp simp: st_tcb_at_kh_if_split st_tcb_def2 active_sc_tcb_at_defs
                        refill_sufficient_kh_def is_refill_sufficient_def
                        refill_ready_kh_def is_refill_ready_def)
  apply (intro conjI impI; drule_tac x=d and y=p in spec2; clarsimp)
        apply (drule_tac x=tptr in bspec, simp, clarsimp)
       apply (drule_tac x=tptr in bspec, simp, clarsimp split: option.splits, auto)+
  apply (drule_tac x=t in bspec, simp, clarsimp split: option.splits, auto)+
  done

(* only called from thread_set_state_eq_valid_sched, which does not seem to be used
lemma thread_set_state_eq_valid_sched_action:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow> (\<And>x. bound (tcb_sched_context (f x))) \<Longrightarrow>
   \<lbrace>valid_sched_action and st_tcb_at ((=) ts) tptr and active_sc_tcb_at tptr\<rbrace>
      thread_set f tptr \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def)
  apply (intro impI conjI allI)
   apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split st_tcb_def2)+

  apply (clarsimp simp:  active_sc_tcb_at_kh_def
                        bound_sc_tcb_at_kh_def obj_at_kh_def obj_at_def active_sc_tcb_at_def
                        pred_tcb_at_def
                  dest!: get_tcb_SomeD)
  apply (intro conjI impI; clarsimp?)
   apply (drule_tac x=tcba in meta_spec)+
   apply (rule_tac x=scp in exI, rule conjI; clarsimp)
  *)

lemma thread_set_state_eq_ct_in_cur_domain:
  "\<lbrakk> \<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x \<rbrakk> \<Longrightarrow>
   \<lbrace>ct_in_cur_domain and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wpsimp
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done
(*
lemma thread_set_state_eq_valid_blocked:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_blocked and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp: dest!: get_tcb_SomeD)
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_def2 active_sc_tcb_at_defs
split: option.splits)
  done*)

(*
context DetSchedSchedule_AI begin
lemma thread_set_state_eq_valid_sched:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow> (\<And>x. bound (tcb_sched_context (f x))) \<Longrightarrow>
   \<lbrace>valid_sched and st_tcb_at ((=) ts) tptr and active_sc_tcb_at tptr\<rbrace>
      thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wp thread_set_state_eq_valid_ready_qs thread_set_state_eq_valid_blocked
            thread_set_state_eq_valid_sched_action thread_set_state_eq_ct_in_cur_domain | simp)+
  done
end
*)
crunch exst[wp]: thread_set "\<lambda>s. P (exst s)"

lemma thread_set_not_idle_valid_idle:
  "\<lbrace>valid_idle and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
     thread_set f tptr \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def, wp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunch valid_sched[wp]: cap_move "valid_sched :: det_state \<Rightarrow> _"

context DetSchedSchedule_AI begin

lemma invoke_cnode_valid_sched:
  "\<lbrace>valid_sched and invs and valid_cnode_inv a and simple_sched_action and valid_ep_q\<rbrace>
     invoke_cnode a
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply wpc
        apply (simp add: liftE_def
               | (wp cancel_badged_sends_valid_sched hoare_vcg_all_lift)+
               | wp_once hoare_drop_imps
               | wpc)+
  apply (fastforce elim: valid_objs_SendEP_distinct dest: invs_valid_objs)
  done

crunches cap_insert, set_extra_badge
 for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
 (wp: hoare_drop_imp simp: do_extended_op_def ignore: do_machine_op)

end

crunches cap_insert
for valid_release_q[wp]:  "valid_release_q::det_state \<Rightarrow> _"
and ct_in_cur_domain[wp]: "ct_in_cur_domain::det_state \<Rightarrow> _"
  (wp: crunch_wps)

crunches sched_context_update_consumed, set_extra_badge
for valid_sched[wp]:  "valid_sched::det_state \<Rightarrow> _"
and not_queued[wp]: "not_queued t"
and not_in_release_q[wp]: "not_in_release_q t"
and active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"
and valid_ready_qs[wp]:  "valid_ready_qs"
and ct_not_in_q[wp]:  "ct_not_in_q"
and valid_sched_action[wp]:  "valid_sched_action"
and ct_in_cur_domain[wp]:  "ct_in_cur_domain"
and etcb_at[wp]:  "etcb_at P t"
and valid_blocked_except_set[wp]:  "valid_blocked_except_set S::det_state \<Rightarrow> _"
and weak_valid_sched_action[wp]:  "weak_valid_sched_action"
  (wp: valid_sched_lift valid_sched_except_blocked_lift valid_blocked_except_set_lift
       weak_valid_sched_action_lift)

crunches set_extra_badge
  for valid_release_q[wp]:  "valid_release_q::det_state \<Rightarrow> _"

lemma sched_context_update_consumed_ko_at_Endpoint[wp]:
  "sched_context_update_consumed scptr \<lbrace>\<lambda>s. Q (ko_at (Endpoint x) p s)\<rbrace>"
  unfolding sched_context_update_consumed_def
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  done

crunches set_extra_badge
for valid_ep_q[wp]:  "valid_ep_q::det_state \<Rightarrow> _"
  (wp: valid_ep_q_lift hoare_vcg_disj_lift)

crunches sched_context_update_consumed
for valid_ep_q[wp]:  "valid_ep_q::det_state \<Rightarrow> _"
  (wp: valid_ep_q_lift hoare_vcg_disj_lift)

crunches  set_extra_badge, cap_insert
  for scheduler_act[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  (wp: crunch_wps)



lemma transfer_caps_lemmas[wp]:
  "\<lbrace>valid_sched\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>not_queued t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>not_in_release_q t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>active_sc_tcb_at t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>budget_ready t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. budget_ready t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>budget_sufficient t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. budget_sufficient t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>valid_blocked_except_set S\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>\<lambda>s. Q (fault_tcb_at P t s)\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv s::det_state. Q (fault_tcb_at P t s)\<rbrace>"
  "\<lbrace>valid_ep_q\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>scheduler_act_sane\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. scheduler_act_sane::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc | (rule hoare_weaken_pre, wps))+
  done

lemma transfer_caps_valid_sched_except_blocked[wp]:
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_idle_etcb::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>ct_in_cur_domain::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  "transfer_caps info caps ep recv recv_buf \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres valid_idle_etcb_lift | wpc)+
  done

lemma possible_switch_to_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and K(target \<noteq> t)\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  by (wpsimp simp: set_scheduler_action_def get_tcb_obj_ref_def thread_get_def
     wp: tcb_sched_enqueue_not_queued reschedule_required_not_queued hoare_vcg_if_lift2
        split_del: if_split)

lemma reply_push_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
             split_del: if_split)

lemma reply_push_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
             split_del: if_split)

context DetSchedSchedule_AI begin

crunch scheduler_act[wp]: do_ipc_transfer "\<lambda>s :: det_state. P (scheduler_action s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

crunches do_ipc_transfer, handle_fault_reply
for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and not_queued[wp]: "not_queued t::det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres )

lemma send_ipc_not_queued_for_timeout:
  "\<lbrace>not_queued t
    and scheduler_act_not t
    and (\<lambda>s. \<forall>xb. ~ (ko_at (Endpoint (RecvEP (t # xb))) (cap_ep_ptr cap) s))\<rbrace>
      send_ipc True False (cap_ep_badge cap) True False tptr (cap_ep_ptr cap)
   \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  by (wpsimp wp: hoare_drop_imp get_simple_ko_wp split_del: if_split )

end

lemma update_sk_obj_ref_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P scp\<rbrace> update_sk_obj_ref C f ref new \<lbrace>\<lambda>_. sc_tcb_sc_at P scp\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
                wp: get_object_wp get_simple_ko_wp)
  apply (clarsimp simp: partial_inv_def sc_tcb_sc_at_def obj_at_def)
  by (case_tac "C ntfn"; clarsimp simp: a_type_def)

context DetSchedSchedule_AI begin

crunch ready_queues[wp]: cap_insert,set_extra_badge,do_ipc_transfer, set_simple_ko, thread_set "\<lambda>s :: det_state. P (ready_queues s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

end

crunches set_thread_state, update_sk_obj_ref
for cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: crunch_wps)


lemma sts_obj_at_send_signal_BOR_helper:
"\<lbrace>\<lambda>s. obj_at (\<lambda>ko. (\<exists>tcb. ko = TCB tcb) \<and>
         active_sc_tcb_at t s \<and> sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) (the sc_caller) s)
            callee s\<rbrace>
       set_thread_state caller st
       \<lbrace>\<lambda>rv s. obj_at (\<lambda>ko. (\<exists>tcb. ko = TCB tcb) \<and>
             active_sc_tcb_at t s \<and> sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) (the sc_caller) s)
                 callee s\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def
        wp: set_object_wp)
  by (auto simp: obj_at_def active_sc_tcb_at_def pred_tcb_at_def sc_tcb_sc_at_def test_sc_refill_max_def
             split: option.splits dest!: get_tcb_SomeD)

lemma obj_at_send_signal_WaitingNtfn_helper:
"\<lbrace>\<lambda>s. obj_at (\<lambda>ko. (\<exists>tcb. ko = TCB tcb) \<and>
         active_sc_tcb_at t s \<and> sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) (the sc_caller) s)
            callee s\<rbrace>
       set_reply_obj_ref f ptr new
       \<lbrace>\<lambda>rv s. obj_at (\<lambda>ko. (\<exists>tcb. ko = TCB tcb) \<and>
             active_sc_tcb_at t s \<and> sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) (the sc_caller) s)
                 callee s\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def
        wp: set_object_wp get_object_wp get_simple_ko_wp)
  by (auto simp: obj_at_def active_sc_tcb_at_def pred_tcb_at_def sc_tcb_sc_at_def test_sc_refill_max_def
             split: option.splits dest!: get_tcb_SomeD)

lemma sts_obj_at_neq:
  "\<lbrace>obj_at P t and K (t\<noteq>t')\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. obj_at P t\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (simp add: pred_tcb_at_def obj_at_def)
  done

lemma sched_context_donate_active_sc_tcb_at_donate_helper:
  "sc_tcb sc = Some a \<Longrightarrow>
  \<lbrace>\<lambda>s::det_state. bound_sc_tcb_at ((=) None) tcb_ptr s \<and>
            test_sc_refill_max sc_ptr s \<and> (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>
     do y <- tcb_sched_action tcb_sched_dequeue a;
        y <- tcb_release_remove a;
        y <- set_tcb_obj_ref tcb_sched_context_update a None;
        test_reschedule a
     od
  \<lbrace>\<lambda>_.  bound_sc_tcb_at ((=) None) tcb_ptr and test_sc_refill_max sc_ptr\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_disj_lift
                 ssc_bound_tcb_at_cases)

lemma sched_context_donate_active_sc_tcb_at_donate:
  "\<lbrace> bound_sc_tcb_at ((=) None) tcb_ptr and test_sc_refill_max sc_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. active_sc_tcb_at tcb_ptr::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
   apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
                       update_sched_context_def set_sc_obj_ref_def
                   wp: get_object_wp hoare_drop_imp set_sc_tcb_update_active_sc_tcb_at)
   apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule sched_context_donate_active_sc_tcb_at_donate_helper, simp)
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def update_sched_context_def set_sc_obj_ref_def
                  wp: get_object_wp hoare_drop_imp set_sc_tcb_update_active_sc_tcb_at)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  done

lemma set_sc_replies_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_ready_qs_def)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=t in bspec)
  apply (simp)
  by (fastforce simp: etcb_defs active_sc_tcb_at_defs refill_prop_defs st_tcb_at_kh_def)

lemma set_sc_replies_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
     (solve_valid_release_q fsimp: st_tcb_at_kh_def)

lemma set_sc_replies_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def
                        switch_in_cur_domain_def in_cur_domain_def)
  apply (intro conjI impI; clarsimp simp: active_sc_tcb_at_defs refill_prop_defs st_tcb_at_kh_def
                                   split: option.splits split del: if_split)
  by (fastforce simp: etcb_defs)+

lemma reply_push_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and not_queued caller and not_queued callee and scheduler_act_not callee\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
                 get_simple_ko_wp set_thread_state_not_queued_valid_ready_qs update_sk_obj_ref_lift
             split_del: if_split cong: conj_cong)

lemma reply_push_valid_release_q[wp]:
  "\<lbrace>valid_release_q and not_in_release_q caller and not_in_release_q callee
              and scheduler_act_not callee and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at ((=) None) callee s)\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  apply (case_tac can_donate; simp)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
                 get_simple_ko_wp sched_context_donate_valid_release_q
                 set_thread_state_not_queued_valid_release_q update_sk_obj_ref_lift
             split_del: if_split cong: conj_cong)+

crunches reply_push
for ct_not_in_q[wp]: "ct_not_in_q"
and not_cur_thread[wp]: "not_cur_thread t"
  (wp: crunch_wps hoare_vcg_if_lift ignore: set_thread_state test_reschedule)

lemma reply_push_valid_sched_helper:
  "\<lbrace> st_tcb_at ((=) Inactive) callee and valid_sched
     and bound_sc_tcb_at ((=) sc_callee) callee \<rbrace>
    when (sc_callee = None \<and> donate) (do
      sc_replies <- liftM sc_replies (get_sched_context sc_ptr);
      y <- case sc_replies of [] \<Rightarrow> assert True
              | r # x \<Rightarrow> do reply <- get_reply r;
                            assert (reply_sc reply = sc_caller);
                            set_reply_obj_ref reply_sc_update r None
                         od;
      y <- set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr # sc_replies);
      y <- set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr);
      sched_context_donate sc_ptr callee
    od)
   \<lbrace> \<lambda>rv. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp add: bind_assoc)
   apply (wpsimp wp: sched_context_donate_valid_sched)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (wpsimp wp: sched_context_donate_valid_sched get_simple_ko_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma reply_push_valid_sched:
  "\<lbrace>st_tcb_at ((=) Inactive) callee and valid_sched and st_tcb_at active caller
     and scheduler_act_not caller and not_queued caller and not_in_release_q caller\<rbrace>
   reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched
                     hoare_drop_imp)
  apply (wpsimp wp: reply_push_valid_sched_helper)
        apply (wpsimp wp: sts_st_tcb_at_other)
        apply (wpsimp wp: reply_push_valid_sched_helper
                          set_thread_state_not_queued_valid_sched
                          set_thread_state_bound_sc_tcb_at)
       apply (wpsimp wp: hoare_drop_imp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_tcb_sc_update_active_sc_tcb_at': (* this is more usable *)
   "\<lbrace>active_sc_tcb_at t and (test_sc_refill_max scp) \<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr (Some scp) \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: set_object_def)
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  by (rule_tac x=scpa in exI, clarsimp)

lemma sched_context_donate_active_sc_tcb_at:
  "\<lbrace>test_sc_refill_max sc_ptr and active_sc_tcb_at t
   and sc_tcb_sc_at (\<lambda>p. p \<noteq> Some t) sc_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def assert_opt_def)
  apply (wpsimp wp: set_tcb_sc_update_active_sc_tcb_at')
       apply (wpsimp wp: set_tcb_sc_update_active_sc_tcb_at_neq)
      apply wpsimp+
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma tcb_sched_context_update_weak_budget_conditions:
  "\<lbrace>is_refill_ready scp 0 and is_refill_sufficient scp 0 \<rbrace>
     set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
   \<lbrace>\<lambda>r s. budget_ready tptr s \<and> budget_sufficient tptr s\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
  using get_tcb_SomeD apply fastforce
  done

lemma sc_tcb_update_budget_conditions:
  "\<lbrace>is_refill_ready scptr 0 and is_refill_sufficient scptr 0 \<rbrace>
     set_sc_obj_ref sc_tcb_update scptr (Some tcb_ptr)
   \<lbrace>\<lambda>xaa s. is_refill_ready scptr 0 s \<and> is_refill_sufficient scptr 0 s\<rbrace>"
  unfolding set_sc_obj_ref_def
  apply (wpsimp wp: set_object_wp get_object_wp simp: update_sched_context_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
  done

crunches reschedule_required
  for budget_conditions_r[wp]: "is_refill_ready scp u"
  and budget_conditions_s[wp]: "is_refill_sufficient scp k"
  (simp: crunch_simps wp: crunch_wps)

crunches tcb_release_remove
  for budget_conditions_r[wp]: "is_refill_ready scp u"
  and budget_conditions_s[wp]: "is_refill_sufficient scp k"
  (simp: is_refill_ready_def is_refill_sufficient_def wp: crunch_wps)

lemma sched_context_donate_weak_budget_conditions:
  "\<lbrace>\<lambda>s. is_refill_ready scp 0 s \<and> is_refill_sufficient scp 0 s\<rbrace>
     sched_context_donate scp tcbptr
   \<lbrace>\<lambda>r s. budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: set_object_wp get_object_wp tcb_sched_context_update_weak_budget_conditions sc_tcb_update_budget_conditions)
  apply (wpsimp wp: set_object_wp get_object_wp simp: test_reschedule_def get_sc_obj_ref_def)+
  done

context DetSchedSchedule_AI begin

lemma send_ipc_valid_sched_helper0:
  "\<lbrace>valid_sched
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
               (active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s))
    and (\<lambda>s. dest \<noteq> idle_thread s)\<rbrace>
   do new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
     y <- assert test;
     y <- set_thread_state dest Running;
     possible_switch_to dest
   od
  \<lbrace>\<lambda>r. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rename_tac new_sc_opt)
  apply (case_tac new_sc_opt; clarsimp simp: bind_assoc )
   apply (wpsimp wp: possible_switch_to_valid_sched_weak set_thread_state_break_valid_sched
                     hoare_vcg_imp_lift sts_st_tcb_at')
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac Q="bound_sc_tcb_at ((=) (Some a)) dest and valid_sched and
           (\<lambda>s. active_sc_tcb_at dest s \<and>
                budget_ready dest s \<and> budget_sufficient dest s) and
            (\<lambda>s. dest \<noteq> idle_thread s)" in hoare_weaken_pre)
   apply (wpsimp wp: possible_switch_to_valid_sched_weak set_thread_state_break_valid_sched
                     hoare_drop_imp sts_st_tcb_at')
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma send_ipc_valid_sched_helper_no_reply:
  "\<lbrace>st_tcb_at ((=) (BlockedOnReceive ep None)) dest and valid_sched and st_tcb_at active tptr
    and (\<lambda>s. not_in_release_q tptr s \<and> scheduler_act_not tptr s \<and> not_queued tptr s)
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
            (active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s))
    and (\<lambda>s. dest \<noteq> idle_thread s) and (\<lambda>s. can_donate \<longrightarrow>
             (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)\<rbrace>
   do
     sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then set_thread_state tptr Inactive
          else when (can_donate \<and> sc_opt = None)
                 (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                     sched_context_donate (the caller_sc_opt) dest
                  od);
     new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
     y <- assert test;
     y <- set_thread_state dest Running;
     possible_switch_to dest
  od
  \<lbrace>\<lambda>r. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: when_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> (\<exists>y. fault = Some y)"; simp split del: if_split)
    (* true for the first if *)
   apply (wpsimp wp: send_ipc_valid_sched_helper0 set_thread_state_not_queued_valid_sched
                     hoare_vcg_disj_lift)
    (* false for the first if *)
  apply (case_tac sc_opt; clarsimp simp: bind_assoc split del: if_split)
   apply (rule_tac Q="obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_fault tcb = None) tptr and
            bound_sc_tcb_at ((=) None) dest and
            st_tcb_at ((=) (BlockedOnReceive ep None)) dest and valid_sched and
             (\<lambda>s. dest \<noteq> idle_thread s) and (\<lambda>s. can_donate \<longrightarrow>
             (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)"
          in hoare_weaken_pre)
    apply (clarsimp simp: bind_assoc)
    apply (rule conjI; clarsimp)
    (* donation happens *)
     apply (rule hoare_seq_ext[OF _ gsc_sp])
     apply (wpsimp wp: hoare_drop_imp set_thread_state_break_valid_sched sts_st_tcb_at'
                       possible_switch_to_valid_sched_weak sched_context_donate_valid_sched
                       sched_context_donate_active_sc_tcb_at_donate
                       sched_context_donate_weak_budget_conditions
                       cong: conj_cong)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
     apply (rename_tac tcb' scp, case_tac "tcb_state tcb'" ; clarsimp)
    (* no donation *)
    by (wpsimp wp: send_ipc_valid_sched_helper0 | simp)+

lemma update_sk_obj_ref_is_refill_ready[wp]:
  "update_sk_obj_ref C f ref new \<lbrace>is_refill_ready scp u::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
                  wp: get_object_wp get_simple_ko_wp)
  apply (clarsimp simp: partial_inv_def is_refill_ready_def obj_at_def)
  by (case_tac "C ntfn"; clarsimp simp: a_type_def)

lemma update_sk_obj_ref_is_refill_sufficient[wp]:
  "update_sk_obj_ref C f ref new \<lbrace>is_refill_sufficient scp 0::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
                  wp: get_object_wp get_simple_ko_wp)
  apply (clarsimp simp: partial_inv_def is_refill_sufficient_def obj_at_def)
  by (case_tac "C ntfn"; clarsimp simp: a_type_def)

lemma set_sc_replies_is_refill_ready[wp]:
  "set_sc_obj_ref sc_replies_update ref list \<lbrace>is_refill_ready scp u::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: is_refill_ready_def obj_at_def)

lemma set_sc_replies_is_refill_sufficient[wp]:
  "set_sc_obj_ref sc_replies_update ref list \<lbrace>is_refill_sufficient scp 0::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: is_refill_sufficient_def obj_at_def)

lemma reply_push_active_sc_tcb_at_helper:
  "\<lbrace> (\<lambda>s. donate \<longrightarrow> (test_sc_refill_max sc_ptr and is_refill_ready sc_ptr 0 and is_refill_sufficient sc_ptr 0) s)
     and bound_sc_tcb_at ((=) None) callee\<rbrace>
    when donate (do
      sc_replies <- liftM sc_replies (get_sched_context sc_ptr);
      y <- case sc_replies of [] \<Rightarrow> assert True
              | r # x \<Rightarrow> do reply <- get_reply r;
                            assert (reply_sc reply = sc_caller);
                            set_reply_obj_ref reply_sc_update r None
                         od;
      y <- set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr # sc_replies);
      y <- set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr);
      sched_context_donate sc_ptr callee
    od)
   \<lbrace> \<lambda>rv s::det_state.
           ((\<not>donate \<longrightarrow> bound_sc_tcb_at ((=) None) callee s) \<and>
            (donate \<longrightarrow> active_sc_tcb_at callee s \<and>
                budget_ready callee s \<and> budget_sufficient callee s)) \<rbrace>"
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp add: bind_assoc)
   by (wpsimp wp: sched_context_donate_active_sc_tcb_at_donate hoare_drop_imp
                     sched_context_donate_weak_budget_conditions)+

lemma reply_push_active_sc_tcb_at:
  "\<lbrace> st_tcb_at ((=) Inactive) callee and
    (\<lambda>s. can_donate \<longrightarrow>
             ( active_sc_tcb_at caller and budget_ready caller and budget_sufficient caller) s)
     and (\<lambda>s. bound_sc_tcb_at ((=) None) callee s \<or>
         active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s)\<rbrace>
     reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv s::det_state. (bound_sc_tcb_at ((=) None) callee s \<or>
         active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s)\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched
                     hoare_vcg_disj_lift set_thread_state_bound_sc_tcb_at hoare_drop_imps)
  apply (case_tac sc_callee; simp)
   apply (rule_tac Q="\<lambda>_ s. ((\<not>can_donate \<longrightarrow> bound_sc_tcb_at ((=) None) callee s) \<and>
                              (can_donate \<longrightarrow> active_sc_tcb_at callee s \<and>
                                  budget_ready callee s \<and> budget_sufficient callee s))"
             in hoare_strengthen_post[rotated], fastforce)
   apply (wpsimp wp: reply_push_active_sc_tcb_at_helper)
     apply (wpsimp wp: hoare_vcg_imp_lift')+
   apply (fastforce simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
  apply (wpsimp wp: sts_st_tcb_at_other hoare_vcg_disj_lift
                    set_thread_state_bound_sc_tcb_at hoare_drop_imps)
  done

lemma reply_push_has_budget_no_donation:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at ((=) None) callee s \<or>
        active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s\<rbrace>
     reply_push caller callee reply_ptr False
   \<lbrace>\<lambda>rv s::det_state. (bound_sc_tcb_at ((=) None) callee s \<or>
         active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s)\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched
                      hoare_vcg_disj_lift set_thread_state_bound_sc_tcb_at hoare_drop_imps)
   apply (wpsimp wp: sts_st_tcb_at_other hoare_vcg_disj_lift
                     set_thread_state_bound_sc_tcb_at hoare_drop_imps)
  done

lemma reply_push_active_sc_tcb_at_no_donation:
  "\<lbrace>active_sc_tcb_at callee\<rbrace>
     reply_push caller callee reply_ptr False
   \<lbrace>\<lambda>rv s::det_state. active_sc_tcb_at callee s \<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched
                      hoare_vcg_disj_lift set_thread_state_bound_sc_tcb_at hoare_drop_imps)
   apply (wpsimp wp: sts_st_tcb_at_other hoare_vcg_disj_lift
                     set_thread_state_bound_sc_tcb_at hoare_drop_imps)
  done

(* FIXME follow up here too *)
lemma send_ipc_valid_sched_helper_some_reply:
  "\<lbrace>(\<lambda>s. \<exists>rptr. st_tcb_at ((=) Inactive) dest s \<and> reply = Some rptr) and valid_sched
       and scheduler_act_not tptr and not_queued tptr and not_in_release_q tptr
       and st_tcb_at active tptr
       and (\<lambda>s. can_donate \<longrightarrow>
             (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)
       and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
                 active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s)
       and (\<lambda>s. dest \<noteq> idle_thread s)\<rbrace>
  do sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then if cg \<and> (\<exists>y. reply = Some y)
               then reply_push tptr dest (the reply) can_donate
               else set_thread_state tptr Inactive
          else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
     new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
     y <- assert test;
     y <- set_thread_state dest Running;
     possible_switch_to dest
   od
   \<lbrace>\<lambda>r. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: when_def split del: if_split)
  apply (case_tac reply; simp split del: if_split)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac sc_opt; clarsimp simp: bind_assoc split del: if_split)
    (* dest has no sc *)
   apply (rule_tac Q="obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_fault tcb = fault) tptr and
             (bound_sc_tcb_at ((=) None) dest and
             ((\<lambda>s. st_tcb_at ((=) Inactive) dest s \<and> valid_sched s) and
              scheduler_act_not tptr and
              not_queued tptr and
              not_in_release_q tptr and
              st_tcb_at active tptr and

              (\<lambda>s. dest \<noteq> idle_thread s) and
              (\<lambda>s. can_donate \<longrightarrow>
             (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)))" in hoare_weaken_pre)
    apply (case_tac "call \<or> (\<exists>y. fault = Some y)"; simp split del: if_split)
    (* true for the first if *)
     apply (clarsimp simp: bind_assoc)
     apply (rule conjI; clarsimp)
    (* reply_push *)
      apply (wpsimp wp: send_ipc_valid_sched_helper0 reply_push_st_tcb_at_Inactive wp_del: reply_push_st_tcb_at)
       apply (wpsimp wp: set_thread_state_break_valid_sched reply_push_valid_sched
                         possible_switch_to_valid_sched_weak sts_st_tcb_at'
                         reply_push_active_sc_tcb_at)
      apply clarsimp
    (* no reply push *)
     apply (wpsimp wp: send_ipc_valid_sched_helper0)
     apply (wpsimp wp: hoare_vcg_disj_lift set_thread_state_not_queued_valid_sched)
     apply clarsimp
    (* false for the first if *)
    apply (clarsimp simp: bind_assoc)
    apply (rule conjI; clarsimp)
    (* donation happens *)
     apply (rule hoare_seq_ext[OF _ gsc_sp])
     apply (wpsimp wp: hoare_drop_imp set_thread_state_break_valid_sched sts_st_tcb_at'
                       possible_switch_to_valid_sched_weak sched_context_donate_valid_sched
                       sched_context_donate_active_sc_tcb_at_donate
                       sched_context_donate_weak_budget_conditions
                 cong: conj_cong)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
    (* dest has no sc (no donation) *)
    apply (wpsimp wp: send_ipc_valid_sched_helper0)
   apply clarsimp
  apply (wpsimp wp: send_ipc_valid_sched_helper0 reply_push_st_tcb_at_Inactive wp_del: reply_push_st_tcb_at)
  apply (wpsimp wp: set_thread_state_break_valid_sched reply_push_valid_sched
                    set_thread_state_not_queued_valid_sched possible_switch_to_valid_sched_strong
                    sts_st_tcb_at' hoare_drop_imp reply_push_active_sc_tcb_at
              cong: conj_cong)+
  apply (wpsimp wp: hoare_vcg_disj_lift)+
  done

crunches do_ipc_transfer
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"
and not_in_release_q[wp]: "\<lambda>s:: det_ext state.  (not_in_release_q t s)"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres simp: crunch_simps)

(* follow up *)
lemma send_ipc_valid_sched_helper:
  "\<lbrace>valid_sched and scheduler_act_not tptr
    and not_queued tptr
    and not_in_release_q tptr and st_tcb_at active tptr
    and (\<lambda>s. can_donate \<longrightarrow>
             (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
           active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s)
    and (\<lambda>s. dest \<noteq> idle_thread s)
    and (\<lambda>s. st_tcb_at (\<lambda>st. \<forall>epptr. \<forall>rp. st = BlockedOnReceive epptr (Some rp)
                             \<longrightarrow> reply_tcb_reply_at (\<lambda>a. a = Some dest) rp s) dest s)\<rbrace>
   do recv_state <- get_thread_state dest;
      reply <- case recv_state of BlockedOnReceive x reply \<Rightarrow>
                         return reply
               | _ \<Rightarrow> fail;
      y \<leftarrow> do_ipc_transfer tptr (Some epptr) ba cg dest;
      y \<leftarrow> maybeM (reply_unlink_tcb dest)     reply;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then if (cg \<and> (\<exists>y. reply = Some y))
                    then reply_push tptr dest (the reply) can_donate
                    else set_thread_state tptr Inactive
           else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
      new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
      y <- assert test;
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac recv_state; simp split del: if_split)
  apply (rename_tac r)
  apply (case_tac r, simp)
   apply (wpsimp wp: send_ipc_valid_sched_helper_no_reply hoare_vcg_imp_lift'
                     hoare_vcg_disj_lift)
   apply assumption
  apply (wpsimp wp: send_ipc_valid_sched_helper_some_reply wp_del: maybeM_wp)
    apply (wpsimp wp: reply_unlink_tcb_valid_sched hoare_vcg_imp_lift'
                      reply_unlink_runnable[simplified runnable_eq_active]
                      hoare_vcg_disj_lift reply_unlink_tcb_bound_sc_tcb_at )
   apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def)
  done

lemma set_simple_ko_pred_tcb_at_state:
  "\<lbrace> \<lambda>s. P (pred_tcb_at proj (f s) t s) \<and> (\<forall>new. f s = f (s\<lparr>kheap := kheap s(ep \<mapsto> new)\<rparr>))\<rbrace>
   set_simple_ko g ep v \<lbrace> \<lambda>_ s. P (pred_tcb_at proj (f s) t s) \<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: get_object_wp simp: set_object_def)
  apply (safe; erule rsubst[where P=P];
         clarsimp split: option.splits simp: pred_tcb_at_def obj_at_def fun_upd_def)
  done

lemma send_ipc_valid_sched:
  "\<lbrace>valid_ep_q and valid_sched and scheduler_act_not thread and not_queued thread
    and not_in_release_q thread and st_tcb_at active thread and invs
    and (\<lambda>s. can_donate \<longrightarrow> (active_sc_tcb_at thread and budget_ready thread and budget_sufficient thread) s)\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases block, simp_all)[1]
     apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong simp: valid_sched_def)
    apply (wpsimp)
   apply (cases block, simp_all)[1]
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong simp: valid_sched_def)
   apply (wpsimp)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: send_ipc_valid_sched_helper set_simple_ko_pred_tcb_at hoare_vcg_disj_lift)
   apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: obj_at_def valid_ep_q_def pred_tcb_at_eq_commute)
  apply (drule_tac x=epptr in spec)
  apply (clarsimp simp: ep_blocked_def pred_tcb_at_def obj_at_def split: option.splits)
  apply (intro conjI)
    apply (clarsimp simp: partial_inv_def cong: conj_cong)
   apply clarsimp
  apply (intro impI; intro conjI)
    apply (fastforce simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: not_cur_thread_def)
  apply (frule invs_valid_objs)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb)
  apply (frule invs_sym_refs)
  apply (drule_tac tp=dest in sym_ref_tcb_reply_Receive)
    apply simp
   apply simp
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb reply_tcb_reply_at_def)
  done

lemma send_ipc_valid_sched_fault:
  "\<lbrace>all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {thread}
    and valid_ep_q and valid_sched and scheduler_act_not thread and not_queued thread
    and not_in_release_q thread and st_tcb_at active thread
    and (\<lambda>s. can_donate \<longrightarrow> (active_sc_tcb_at thread and budget_ready thread and budget_sufficient thread) s)\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases block, simp_all)[1]
     apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong simp: valid_sched_def)
    apply (wpsimp)
   apply (cases block, simp_all)[1]
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong simp: valid_sched_def)
   apply (wpsimp)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: send_ipc_valid_sched_helper set_simple_ko_pred_tcb_at hoare_vcg_disj_lift)
   apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: obj_at_def valid_ep_q_def pred_tcb_at_eq_commute)
  apply (drule_tac x=epptr in spec)
  apply (clarsimp simp: ep_blocked_def pred_tcb_at_def obj_at_def split: option.splits)
  apply (intro conjI)
    apply (clarsimp simp: partial_inv_def cong: conj_cong)
   apply clarsimp
  apply (intro impI; intro conjI)
    apply (fastforce simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: not_cur_thread_def)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb)
  apply (drule_tac tp=dest in sym_ref_tcb_reply_Receive)
    apply simp
   apply simp
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb reply_tcb_reply_at_def)
  done

end

lemma thread_set_ep_at_pred[wp]:
  "thread_set f tptr \<lbrace>\<lambda>s. Q (ep_at_pred P p s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: simple_obj_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_sc_budget_conditions[wp]:
  "thread_set f t \<lbrace>\<lambda>s. Q (test_sc_refill_max scp s)\<rbrace>"
  "thread_set f t \<lbrace>\<lambda>s. Q (is_refill_ready scp 0 s)\<rbrace>"
  "thread_set f t \<lbrace>\<lambda>s. Q (is_refill_sufficient scp 0 s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp, clarsimp simp: test_sc_refill_max_def dest!: get_tcb_SomeD)
  apply (wpsimp wp: thread_set_wp, clarsimp simp: is_refill_ready_def obj_at_def dest!: get_tcb_SomeD)
  apply (wpsimp wp: thread_set_wp, clarsimp simp: is_refill_sufficient_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_valid_ep_q:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
  \<lbrace>valid_ep_q\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_ep_q\<rbrace>"
  unfolding valid_ep_q_def2
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' thread_set_no_change_tcb_pred_gen
                 hoare_vcg_disj_lift hoare_vcg_ex_lift
           simp: bound_sc_budget_conditions_equiv)

context DetSchedSchedule_AI begin

lemma send_fault_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched and st_tcb_at active tptr and scheduler_act_not tptr and valid_ep_q
     and not_queued tptr and (ct_active or ct_idle) and invs and (\<lambda>_. valid_fault fault)
     and not_in_release_q tptr
     and (\<lambda>s. can_donate \<longrightarrow> (active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr) s)\<rbrace>
    send_fault_ipc tptr handler_cap fault can_donate
     \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases "valid_fault fault"; simp)
  apply (simp add: send_fault_ipc_def Let_def)
  apply (case_tac handler_cap; simp)
   by (wpsimp wp: send_ipc_valid_sched_fault
                  thread_set_not_state_valid_sched
                  thread_set_no_change_tcb_state
                  thread_set_invs_but_fault_tcbs
                  thread_set_valid_ep_q
                  thread_set_active_sc_tcb_at
                  budget_ready_thread_set_no_change
                  budget_sufficient_thread_set_no_change
                  hoare_vcg_imp_lift)+

end

lemma handle_no_fault_valid_ready_qs:
  "\<lbrace>valid_ready_qs and not_queued tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_no_fault_def set_thread_state_def)
  apply (wp | simp add: set_object_def)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def
                        refill_sufficient_kh_def is_refill_sufficient_def
                        refill_ready_kh_def is_refill_ready_def
                 dest!: get_tcb_SomeD)
  apply (drule_tac x=d and y=p in spec2,clarsimp,  drule_tac x=t in bspec, simp)
  apply (clarsimp simp: active_sc_tcb_at_defs, intro conjI impI, fastforce+)
    apply (rename_tac scp, rule_tac x=scp in exI, fastforce)+
  done

lemma handle_no_fault_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_no_fault_def set_thread_state_def)
  apply (wp | simp add: set_object_def)+
  by (clarsimp simp: not_in_release_q_def
               dest!: get_tcb_SomeD) solve_valid_release_q

lemma handle_no_fault_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: handle_no_fault_def wp: set_thread_state_act_not_valid_sched_action)

lemma handle_no_fault_valid_sched:
  "\<lbrace>valid_sched and not_queued tptr and not_in_release_q tptr and  scheduler_act_not tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def)
  including no_pre
  apply (wp handle_no_fault_valid_ready_qs handle_no_fault_valid_sched_action
            set_thread_state_valid_blocked_const handle_no_fault_valid_release_q
          | rule hoare_conjI | simp add: handle_no_fault_def | fastforce simp: simple_sched_action_def)+
  done

lemma send_fault_ipc_error_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_cur_thread[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

context DetSchedSchedule_AI begin

lemma send_ipc_not_queued:
  "\<lbrace>not_queued tcb_ptr and scheduler_act_not tcb_ptr and (\<lambda>s. \<forall>qtail. \<not>ko_at (Endpoint (RecvEP (tcb_ptr # qtail))) epptr s)\<rbrace>
   send_ipc True False badge True can_donate tptr epptr
   \<lbrace>\<lambda>rv. not_queued tcb_ptr::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def )
  apply (wpsimp wp: hoare_drop_imp get_simple_ko_wp
         split_del: if_split
              simp: do_ipc_transfer_def do_normal_transfer_def)
  done

crunches reply_push
  for not_in_release_q'[wp]: "\<lambda>s::det_state. not_in_release_q t s"
  and etcb_at[wp]: "etcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma send_ipc_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace> send_ipc True False badge True can_donate tptr epptr  \<lbrace>\<lambda>rv. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def )
  by (wpsimp wp: hoare_drop_imp get_simple_ko_wp
      split_del: if_split
           simp: do_ipc_transfer_def do_normal_transfer_def)

crunches set_extra_badge, copy_mrs
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma transfer_caps_loop_scheduler_action:
  "transfer_caps_loop h x2 m xd dest_slots mi'
       \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  apply (induction rule: transfer_caps_loop.induct; simp)
  apply safe
  apply (wpsimp | assumption)+
  done

lemma transfer_caps_scheduler_action[wp]:
  "transfer_caps xc xd (Some x31) x21 x \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  unfolding transfer_caps_def
  by (wpsimp wp: transfer_caps_loop_scheduler_action)

lemma transfer_caps_scheduler_act_not:
  "\<lbrace>scheduler_act_not t and (\<lambda>s. \<forall>xb. \<not>ko_at (Endpoint (RecvEP (t # xb))) epptr s)\<rbrace>
   send_ipc True False badge True can_donate tptr epptr
   \<lbrace>\<lambda>rv. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def )
  apply (wpsimp wp: hoare_drop_imps
         split_del: if_split
              simp: do_ipc_transfer_def do_normal_transfer_def do_fault_transfer_def)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)
    apply clarsimp
    apply (wpsimp wp: get_simple_ko_wp)+
  done

lemma send_fault_ipc_not_queued:
  "\<lbrace>invs and not_queued t and st_tcb_at active t and scheduler_act_not t\<rbrace>
   send_fault_ipc tptr handler_cap fault can_donate
   \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift_R send_ipc_not_queued)
               apply (wpsimp wp: thread_set_wp)+
  apply (subgoal_tac "st_tcb_at (not active) t s")
   apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  apply (subgoal_tac "ko_at (Endpoint (RecvEP (t # qtail))) x s")
   apply (rule ep_queued_st_tcb_at; clarsimp?)
     apply assumption
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (rule refl)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def split: if_splits)
  done

lemma send_fault_ipc_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate \<lbrace>\<lambda>rv. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R send_ipc_not_in_release_q)+ | wpc)+

lemma send_fault_ipc_scheduler_act_not:
  "\<lbrace>invs and st_tcb_at active t and scheduler_act_not t\<rbrace>
   send_fault_ipc tptr handler_cap fault can_donate
   \<lbrace>\<lambda>rv. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift_R transfer_caps_scheduler_act_not)
               apply (wpsimp wp: thread_set_wp)+
  apply (subgoal_tac "st_tcb_at (not active) t s")
   apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  apply (subgoal_tac "ko_at (Endpoint (RecvEP (t # xba))) x s")
   apply (rule ep_queued_st_tcb_at; clarsimp?)
     apply assumption
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (rule refl)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def split: if_splits)
  done

crunches update_sk_obj_ref
  for valid_sched_action[wp]: "valid_sched_action:: det_state \<Rightarrow> _"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain:: det_state \<Rightarrow> _"
  and valid_blocked_except_set[wp]: "valid_blocked_except_set S:: det_state \<Rightarrow> _"

lemma reply_push_valid_sched_no_donation:
  "\<lbrace> valid_sched_except_blocked and valid_blocked_except thread and not_in_release_q thread and
     scheduler_act_not thread and not_queued thread\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_not_queued_valid_sched_strong hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma reply_push_weak_valid_sched_action_no_donation:
  "\<lbrace> weak_valid_sched_action and
     scheduler_act_not thread\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_act_not_weak_valid_sched_action hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma reply_push_valid_blocked_no_donation:
  "\<lbrace> valid_blocked_except_set (insert thread S)\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked_remove hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma reply_push_valid_blocked_no_donation':
  "\<lbrace> valid_blocked\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked_remove hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma sched_context_update_consumed_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def update_sched_context_def set_object_def
             wp: get_object_wp)
     solve_valid_release_q

crunches sched_context_update_consumed
for valid_sched_except_blocked[wp]: "valid_sched_except_blocked"
  (wp: crunch_wps )

crunches do_ipc_transfer
  for valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
  and valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
  and valid_sched_action[wp]: "valid_sched_action::det_state \<Rightarrow> _"
  and ct_not_in_q[wp]: "ct_not_in_q::det_state \<Rightarrow> _"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain::det_state \<Rightarrow> _"
  and weak_valid_sched_action[wp]: "weak_valid_sched_action::det_state \<Rightarrow> _"
  and valid_sched_except_blocked[wp]: "valid_sched_except_blocked::det_state \<Rightarrow> _"
  and valid_blocked_except_set[wp]: "valid_blocked_except_set S::det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp)

crunches do_ipc_transfer
  for valid_idle_etcb[wp]: "valid_idle_etcb::det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp wp_del: valid_idle_etcb_lift)

lemmas do_ipc_transfer_valid_blocked[wp] = do_ipc_transfer_valid_blocked_except_set[where S="{}"]

crunches do_ipc_transfer
  for not_queued[wp]: "(not_queued t)::det_state \<Rightarrow> _"
  and not_in_release_q[wp]: "(not_in_release_q t)::det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp)

lemma weak_valid_sched_action_scheduler_action_not:
  "weak_valid_sched_action s \<Longrightarrow> st_tcb_at (not runnable) t s \<Longrightarrow> scheduler_act_not t s"
  by (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def pred_neg_def
                     pred_tcb_at_def obj_at_def)

lemma valid_release_q_not_in_release_q_not_runnable:
  "valid_release_q s \<Longrightarrow> st_tcb_at (not runnable) t s \<Longrightarrow> not_in_release_q t s"
  apply (clarsimp simp: valid_release_q_def not_in_release_q_def pred_neg_def
                     pred_tcb_at_def obj_at_def)
  apply fastforce
  done

lemma valid_ready_qs_not_queued_not_runnable:
  "valid_ready_qs s \<Longrightarrow> st_tcb_at (not runnable) t s \<Longrightarrow> not_queued t s"
  apply (clarsimp simp: valid_ready_qs_def not_queued_def pred_neg_def
                     pred_tcb_at_def obj_at_def)
  apply fastforce
  done
(*
lemma refill_ready_wp:
  "\<lbrace>\<lambda>s. P (is_refill_ready ptr 0 s) s\<rbrace> refill_ready ptr \<lbrace>P\<rbrace>"
  unfolding refill_ready_def
  apply wpsimp
  apply (clarsimp simp: is_refill_ready_def obj_at_def)
  done

lemma refill_sufficient_wp:
  "\<lbrace>\<lambda>s. P (is_refill_sufficient ptr usage s) s\<rbrace> refill_sufficient ptr usage \<lbrace>P\<rbrace>"
  unfolding refill_sufficient_def
  apply (wpsimp wp: get_refills_wp)
  apply (clarsimp simp: is_refill_sufficient_def obj_at_def)
  done
*)
lemma possible_switch_to_valid_blocked:
  "\<lbrace>valid_blocked_except_set (insert target S)\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_enqueue
                    reschedule_required_valid_blocked
                    set_scheduler_action_valid_blocked_except_set_remove)
  apply safe
    apply clarsimp
   apply (clarsimp simp: valid_blocked_def valid_blocked_except_set_def pred_tcb_at_eq_commute)+
   apply (drule_tac x=t in spec, clarsimp)
   apply (fastforce simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_set_def pred_tcb_at_eq_commute)
  apply (drule_tac x=t in spec, clarsimp)
  apply (fastforce simp: not_in_release_q_def in_release_queue_def)
  done

lemma has_budget_def2:
  "has_budget t s = has_budget_kh t (cur_time s) (kheap s)"
  by (clarsimp simp: has_budget_def)

(* FIXME Move *)
lemma set_thread_state_runnable_valid_blocked_except_set_inc:
  "\<lbrace>valid_blocked_except_set S and (\<lambda>s. runnable ts) and (\<lambda>s. st_tcb_at (not runnable) ref s) and
      (\<lambda>s. \<not> (ref \<in> S \<or> in_ready_q ref s \<or> in_release_q ref s \<or> ref = cur_thread s
                  \<or> scheduler_action s = switch_thread ref \<or> (\<not> active_sc_tcb_at ref s)))\<rbrace>
    set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_blocked_except_set (insert ref S)::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: set_scheduler_action_wp is_schedulable_wp set_object_wp)
  by (fastforce simp: valid_blocked_except_set_def active_sc_tcb_at_defs st_tcb_at_kh_def
              split: option.splits if_splits dest!: get_tcb_SomeD)

(* FIXME move *)
lemma valid_ready_qs_not_runnable_not_inq:
  "\<lbrakk>valid_ready_qs s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s"
  by (fastforce simp: valid_ready_qs_def pred_tcb_at_def not_queued_def obj_at_def)

(* FIXME move *)
lemma valid_release_q_not_runnable_not_inq:
  "\<lbrakk>valid_release_q s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (fastforce simp: valid_release_q_def pred_tcb_at_def not_in_release_q_def obj_at_def)


lemma send_ipc_valid_sched_subset_for_handle_timeout:
  "\<lbrace>valid_release_q and valid_ready_qs and weak_valid_sched_action and valid_blocked and valid_idle_etcb
    and not_in_release_q thread and not_queued thread and valid_ep_q and scheduler_act_not thread
    and tcb_at thread\<rbrace>
   send_ipc True False badge True False thread epptr
   \<lbrace>\<lambda>rv. (valid_release_q and
               valid_ready_qs and
               weak_valid_sched_action and valid_blocked and valid_idle_etcb)::det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (wpsimp wp: set_thread_state_not_queued_valid_release_q
                      set_thread_state_not_queued_valid_ready_qs set_thread_state_act_not_weak_valid_sched_action
                      set_thread_state_not_runnable_valid_blocked)
   apply (wpsimp wp: set_thread_state_not_queued_valid_release_q
                     set_thread_state_not_queued_valid_ready_qs set_thread_state_act_not_weak_valid_sched_action
                     set_thread_state_not_runnable_valid_blocked)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply wpsimp
               apply (wpsimp wp: possible_switch_to_valid_ready_qs possible_switch_to_valid_blocked)
              apply (wpsimp wp: sts_st_tcb_at' hoare_vcg_disj_lift set_thread_state_runnable_valid_release_q
                                set_thread_state_runnable_valid_ready_qs
                                set_thread_state_runnable_weak_valid_sched_action set_thread_state_valid_blocked_const)
             apply wpsimp
            apply (wpsimp wp: refill_ready_wp refill_sufficient_wp)
           apply (wpsimp wp: get_tcb_obj_ref_wp)
          apply (rule_tac Q="\<lambda>_. valid_release_q and valid_ready_qs and weak_valid_sched_action
                             and valid_blocked and valid_idle_etcb and tcb_at dest
                             and (\<lambda>b. bound_sc_tcb_at ((=) None) dest b \<or>
                             active_sc_tcb_at dest b \<and>
                             budget_ready dest b \<and>
                             budget_sufficient dest b)" in hoare_strengthen_post[rotated])
           apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def, fastforce)
          apply wpsimp
            apply (wpsimp wp: reply_push_weak_valid_sched_action_no_donation reply_push_valid_blocked_no_donation'
                              reply_push_typ_at tcb_at_typ_at reply_push_has_budget_no_donation valid_idle_etcb_lift)
           apply (wpsimp wp: set_thread_state_not_queued_valid_release_q
                             set_thread_state_not_queued_valid_ready_qs set_thread_state_act_not_weak_valid_sched_action
                             set_thread_state_not_runnable_valid_blocked hoare_vcg_disj_lift)
          apply wpsimp
         apply (wpsimp wp: thread_get_wp)
        apply (wpsimp wp: get_tcb_obj_ref_wp)
       apply (rule_tac Q="\<lambda>r. valid_release_q and valid_ready_qs and weak_valid_sched_action and valid_blocked and valid_idle_etcb
                              and not_in_release_q thread and not_in_release_q dest
                              and not_queued thread and not_queued dest and scheduler_act_not thread and
                              scheduler_act_not dest  and tcb_at dest and tcb_at thread and
                              (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
                              active_sc_tcb_at dest s \<and>
                              budget_ready dest s \<and> budget_sufficient dest s)"
              in hoare_strengthen_post[rotated])
        apply clarsimp
       apply (wpsimp wp: reply_unlink_tcb_valid_release_q reply_unlink_tcb_valid_ready_qs
                         reply_unlink_tcb_valid_blocked_except_set
                         reply_unlink_tcb_weak_valid_sched_action hoare_vcg_disj_lift)
      apply (rule_tac Q="\<lambda>r. valid_release_q and valid_ready_qs and weak_valid_sched_action and valid_blocked and valid_idle_etcb
                             and not_in_release_q thread and not_in_release_q dest
                             and not_queued thread and not_queued dest and scheduler_act_not thread and
                             scheduler_act_not dest and tcb_at dest and tcb_at thread and
                              (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
                              active_sc_tcb_at dest s \<and>
                              budget_ready dest s \<and> budget_sufficient dest s)"
             in hoare_strengthen_post[rotated])
       (* probably should exchange budget information for valid_ep_q at this point *)
       apply (clarsimp simp: obj_at_def pred_tcb_at_def is_tcb has_budget_equiv)
      apply (wpsimp wp: hoare_vcg_disj_lift reply_unlink_tcb_valid_release_q)
     apply (wpsimp wp: )
    apply (wpsimp wp: gts_wp)
   apply clarsimp
   apply (rule_tac Q="\<lambda>r. valid_release_q and valid_ready_qs and weak_valid_sched_action
                          and valid_blocked and valid_idle_etcb
                          and tcb_at thread and not_queued thread and
                     (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
                     active_sc_tcb_at dest s \<and>
                     budget_ready dest s \<and> budget_sufficient dest s) and
                          (\<lambda>s. not_in_release_q thread s \<and> scheduler_act_not thread s)"
          in hoare_strengthen_post[rotated])
    apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)
    apply (intro conjI)
      apply (erule valid_release_q_not_in_release_q_not_runnable; (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)?)
     apply (erule valid_ready_qs_not_queued_not_runnable; (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)?)
    apply (erule weak_valid_sched_action_scheduler_action_not; (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)?)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  apply (clarsimp simp: valid_ep_q_def obj_at_def)
  apply (drule_tac x=epptr in spec)
  apply clarsimp
  done


lemma send_ipc_valid_sched_for_handle_timeout:
  "\<lbrace>all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {thread}
    and valid_sched_except_blocked and valid_blocked_except thread
    and fault_tcb_at bound thread and valid_ep_q
    and (\<lambda>s. not_in_release_q thread s \<and>  scheduler_act_not thread s \<and> not_queued thread s)\<rbrace>
   send_ipc True False badge True False thread epptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: send_ipc_valid_sched_helper0)
            apply (wpsimp wp: reply_push_valid_sched_no_donation reply_push_has_budget_no_donation)
           apply (wpsimp wp: set_thread_state_not_queued_valid_sched_strong)
           apply (wpsimp wp: hoare_vcg_disj_lift)
          apply (wpsimp wp: thread_get_wp)+
       apply (rule_tac Q="\<lambda>r. (valid_sched_except_blocked and
                               valid_blocked_except_set {thread}) and fault_tcb_at bound thread
                               and not_in_release_q thread and
                               scheduler_act_not thread and not_queued thread and
                               (\<lambda>s.
                               (bound_sc_tcb_at ((=) None) dest s \<or>
                                active_sc_tcb_at dest s \<and>
                                budget_ready dest s \<and> budget_sufficient dest s) \<and>
                               not_cur_thread dest s \<and> dest \<noteq> idle_thread s)"
                               in hoare_strengthen_post[rotated])
        apply (clarsimp simp: obj_at_def pred_tcb_at_def)
       apply (wpsimp wp: reply_unlink_tcb_valid_sched_except_blocked reply_unlink_tcb_valid_blocked_except_set
                         hoare_vcg_disj_lift)
      apply (rule_tac Q="\<lambda>r. (valid_sched_except_blocked and
                              valid_blocked_except_set {thread}) and fault_tcb_at bound thread and
                              (\<lambda>s. not_in_release_q thread s \<and>
                 scheduler_act_not thread s \<and> not_queued thread s) and
                              (\<lambda>s. \<forall>x. reply = Some x \<longrightarrow> reply_tcb_reply_at (\<lambda>x. x = Some dest) x s) and
                              (\<lambda>s.
                              (bound_sc_tcb_at ((=) None) dest s \<or>
                               active_sc_tcb_at dest s \<and>
                               budget_ready dest s \<and> budget_sufficient dest s) \<and>
                              not_cur_thread dest s \<and> dest \<noteq> idle_thread s)"
                              in hoare_strengthen_post[rotated])
       apply (clarsimp simp: obj_at_def pred_tcb_at_def)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
     apply (wpsimp wp: )
    apply (wpsimp wp: gts_wp)
   apply clarsimp
   apply (rule_tac Q="\<lambda>r. (valid_sched_except_blocked and
                           valid_blocked_except_set {thread}) and fault_tcb_at bound thread and
                           (\<lambda>s. not_in_release_q thread s \<and>
              scheduler_act_not thread s \<and> not_queued thread s) and
                           (\<lambda>s. \<forall>a x. st_tcb_at ((=) (BlockedOnReceive a (Some x))) dest s
                                      \<longrightarrow> reply_tcb_reply_at (\<lambda>x. x = Some dest) x s) and
                           (\<lambda>s.
                           (bound_sc_tcb_at ((=) None) dest s \<or>
                            active_sc_tcb_at dest s \<and>
                            budget_ready dest s \<and> budget_sufficient dest s) \<and>
                           not_cur_thread dest s \<and> dest \<noteq> idle_thread s)"
                           in hoare_strengthen_post[rotated])
    apply (clarsimp simp: obj_at_def )
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  apply (clarsimp simp: valid_ep_q_def obj_at_def)
  apply (drule_tac x=epptr in spec)
  apply (clarsimp simp: not_cur_thread_def)
  apply (intro conjI)
   apply clarsimp
   apply (erule BlockedOnReceive_reply_tcb_reply_at; clarsimp)
  apply fastforce
  done

lemma set_thread_fault_active_sc_tcb_at[wp]:
  "thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule subst[rotated, where P=P])
  apply (clarsimp simp: active_sc_tcb_at_def test_sc_refill_max_def pred_tcb_at_def obj_at_def
                  dest!: get_tcb_SomeD
                   cong: conj_cong)
  apply fastforce
  done

lemma set_thread_fault_etcbs_of[wp]:
  "\<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_ s. P (etcbs_of s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule subst[rotated, where P=P])
  apply (fastforce simp:etcbs_of'_def dest!: get_tcb_SomeD)
  done

lemma set_thread_fault_budget_ready[wp]:
  "\<lbrace>budget_ready t\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_refill_ready_def dest!: get_tcb_SomeD cong: conj_cong)
  done

lemma set_thread_fault_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient t\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def dest!: get_tcb_SomeD cong: conj_cong)
  done

lemma set_thread_fault_cur_domain[wp]:
  "thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by (wpsimp wp: thread_set_wp)

lemma set_thread_fault_valid_sched_except_blocked[wp]:
  "\<lbrace>valid_release_q\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  "\<lbrace>valid_ready_qs\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  "\<lbrace>valid_sched_action\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  "\<lbrace>weak_valid_sched_action\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  "\<lbrace>ct_in_cur_domain\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_ready_qs_lift valid_release_q_lift valid_sched_action_lift weak_valid_sched_action_lift
                 ct_in_cur_domain_lift thread_set_no_change_tcb_pred)+

lemma set_thread_fault_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_blocked_except_set_lift thread_set_no_change_tcb_pred)

lemma set_thread_fault_valid_ep_q[wp]:
  "\<lbrace>valid_ep_q\<rbrace> thread_set (tcb_fault_update (\<lambda>_. fopt)) tptr \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  apply (wpsimp wp: valid_ep_q_lift)
  apply (wpsimp wp: thread_set_wp simp: obj_at_def)
  apply (wpsimp wp: hoare_vcg_disj_lift thread_set_no_change_tcb_pred)+
  done

lemma send_fault_ipc_valid_sched_for_handle_timeout:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except tptr and scheduler_act_not tptr
    and not_queued tptr and not_in_release_q tptr and valid_ep_q and invs and K (valid_fault fault)
    and K (is_ep_cap handler_cap)\<rbrace>
     send_fault_ipc tptr handler_cap fault False
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases "valid_fault fault"; simp)
  apply (simp add: send_fault_ipc_def Let_def)
  apply (case_tac handler_cap; simp)
  by (wpsimp wp: send_ipc_valid_sched_for_handle_timeout
                 thread_set_invs_but_fault_tcbs
                 thread_set_pred_tcb_at_sets_true)+

lemma handle_timeout_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except tptr
     and scheduler_act_not tptr and K (valid_fault ex)
     and not_in_release_q tptr and not_queued tptr and invs and valid_ep_q\<rbrace>
     handle_timeout tptr ex
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  by (wpsimp wp: send_fault_ipc_valid_sched_for_handle_timeout assert_wp)


lemma refill_unblock_check_ko_at_Endpoint[wp]:
  "refill_unblock_check param_a \<lbrace>\<lambda>s. Q (ko_at (Endpoint x) p s)\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp simp: wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  by  (clarsimp simp: obj_at_def)

lemma refill_unblock_check_valid_ep_q[wp]:
  "\<lbrace>valid_ep_q and valid_machine_time\<rbrace> refill_unblock_check param_a \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  by (wpsimp wp: valid_ep_q_lift_pre_conj[where R=valid_machine_time] hoare_vcg_disj_lift)

(*
lemma set_thread_state_runnable_valid_blocked2:  (* ref should be queued *)
  "\<lbrace>valid_blocked
    and (st_tcb_at runnable ref or (\<lambda>s. ~ active_sc_tcb_at ref s))
    and (\<lambda>s. runnable ts)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp simp: get_tcb_rev active_sc_tcb_at_defs st_tcb_at_kh_if_split
      split: option.splits if_splits)
  apply (case_tac "tcb_state y"; clarsimp)
  done
*)
lemma set_thread_state_runnable_valid_sched2:
  "\<lbrace>valid_sched
    and (st_tcb_at runnable ref or (\<lambda>s. ~ active_sc_tcb_at ref s))
    and (\<lambda>s. runnable ts)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_thread_state_runnable_valid_ready_qs
                 set_thread_state_valid_blocked_const
                 set_thread_state_runnable_valid_sched_action
                 set_thread_state_runnable_valid_release_q simp: valid_sched_def)
    (clarsimp simp: valid_blocked_def pred_tcb_at_def obj_at_def, case_tac "tcb_state tcb"; fastforce)

lemma tcb_fault_update_valid_ep_q[wp]:
  "thread_set (tcb_fault_update tf) tptr \<lbrace>valid_ep_q\<rbrace>"
  apply (wpsimp wp: valid_ep_q_lift thread_set_no_change_tcb_pred)
     apply (wpsimp wp: thread_set_wp)
     apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD split: if_splits)
    apply (wpsimp wp: thread_set_no_change_tcb_pred hoare_vcg_disj_lift active_sc_tcb_at_thread_set_no_change
                      budget_sufficient_thread_set_no_change budget_ready_thread_set_no_change)+
  done


lemma bound_sc_tcb_at_kh_eq_commute:
  "bound_sc_tcb_at_kh ((=) None) t kh = bound_sc_tcb_at_kh (\<lambda>st. st = None) t kh"
  by (auto simp: bound_sc_tcb_at_kh_def obj_at_kh_def)

lemma set_thread_state_valid_ep_q:
  "\<lbrace> valid_ep_q
     and st_tcb_at (\<lambda>ts. (\<forall>eptr r_opt. ts ~= BlockedOnReceive eptr r_opt) \<and>
                         (\<forall>eptr pl. ts ~= BlockedOnSend eptr pl)) thread\<rbrace>
    set_thread_state thread ts
   \<lbrace> \<lambda>_. valid_ep_q \<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ep_q_def dest!: get_tcb_SomeD split: option.splits)
  apply (case_tac x2; clarsimp)
  apply (drule_tac x=p in spec; clarsimp)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def)
  apply (clarsimp simp: pred_tcb_at_eq_commute sc_at_pred_n_eq_commute
                        bound_sc_tcb_at_kh_eq_commute)
  apply (auto simp: active_sc_tcb_at_defs refill_sufficient_kh_def refill_ready_kh_def
                    is_refill_sufficient_def is_refill_ready_def
             split: if_splits option.splits cong: conj_cong)
  done

lemma  as_user_valid_ep_q[wp]:
  "\<lbrace>valid_ep_q\<rbrace> as_user param_a param_b \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
 apply (wpsimp wp: as_user_wp_thread_set_helper thread_set_wp)
 apply (clarsimp simp: valid_ep_q_def obj_at_kh_def st_tcb_at_kh_def
                dest!: get_tcb_SomeD split: option.splits)
  apply (case_tac x2; clarsimp)
  apply (drule_tac x=p in spec)
  apply (drule_tac x="Endpoint x3" in spec)
  apply (clarsimp simp: )
  apply (drule_tac bspec, assumption)
  apply (clarsimp simp: pred_tcb_at_eq_commute)
  apply (intro conjI)
  apply (case_tac x3; clarsimp simp: pred_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def)
  apply (erule disjE)
  apply (clarsimp simp: bound_sc_tcb_at_kh_def obj_at_kh_def test_sc_refill_max_kh_def
                        pred_tcb_at_def obj_at_def
                  cong: conj_cong split: option.splits)
  apply (fastforce simp: active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_def obj_at_kh_def
                         test_sc_refill_max_kh_def pred_tcb_at_def obj_at_def active_sc_tcb_at_def
                         test_sc_refill_max_def refill_sufficient_kh_def is_refill_sufficient_def
                         refill_ready_kh_def is_refill_ready_def
                 cong: conj_cong split: option.splits)
  done

crunches do_ipc_transfer
  for valid_ep_q[wp]: "\<lambda>s::det_state. valid_ep_q s"
  (wp: crunch_wps)

crunches handle_fault_reply
for active_sc_tcb_at[wp]: "\<lambda>s::det_state. active_sc_tcb_at a s"
and not_in_release_q[wp]: "\<lambda>s::det_state. not_in_release_q x s"
and simple_sched_action[wp]: "\<lambda>s::det_state. simple_sched_action s"
and valid_ep_q[wp]: "\<lambda>s::det_state. valid_ep_q s"
and cur_thread[wp]:"\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres )

lemma set_reply_Endpoint_ko_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) pa s)\<rbrace> set_reply p r \<lbrace>\<lambda>_ s. Q (ko_at (Endpoint ep) pa s)\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_wp get_object_wp)

lemma set_reply_valid_ep_q[wp]:
  "\<lbrace>valid_ep_q\<rbrace> set_reply p r \<lbrace>\<lambda>_. valid_ep_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_ep_q_lift set_simple_ko_pred_tcb_at hoare_vcg_disj_lift)

lemma reply_unlink_tcb_valid_ep_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. \<forall>a. reply_tcb_reply_at (\<lambda>recv_opt. recv_opt = Some a) r s \<longrightarrow>
                          st_tcb_at ((=) (BlockedOnReply r)) a s)\<rbrace>
    reply_unlink_tcb t r
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def pred_tcb_at_eq_commute
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: set_thread_state_valid_ep_q update_sk_obj_ref_lift)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_at_ppred_def)
  done

lemma set_sc_obj_ref_ko_at_Endpoint[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    set_sc_obj_ref f scp replies
   \<lbrace>\<lambda>_ s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding set_sc_obj_ref_def
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  done

lemma update_sk_obj_ref_Reply_ko_at_Endpoint[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
   update_sk_obj_ref Reply update ref new
   \<lbrace>\<lambda>a s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma reply_unlink_sc_valid_ep_q:
  "\<lbrace>valid_ep_q\<rbrace>
    reply_unlink_sc scp r
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_sc_def
  apply wpsimp
         apply (wpsimp wp: valid_ep_q_lift hoare_vcg_disj_lift )+
        apply fastforce
       apply (wpsimp wp: valid_ep_q_lift hoare_vcg_disj_lift
                         active_sc_tcb_at_update_sched_context_no_change
                         budget_ready_update_sched_context_no_change
                         budget_sufficient_update_sched_context_no_change)+
  done

lemma tcb_sched_context_update_valid_ep_q_not_in_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. \<forall>ep epptr. ko_at (Endpoint ep) epptr s \<longrightarrow> caller \<notin> set (ep_queue ep))\<rbrace>
       set_tcb_obj_ref tcb_sched_context_update caller scopt
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ep_q_def split:option.splits kernel_object.splits
                 dest!: get_tcb_SomeD)
  apply (drule_tac x=p in spec; clarsimp)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (intro conjI)
   apply (case_tac x3; clarsimp simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
   apply (clarsimp simp: active_sc_tcb_at_defs refill_sufficient_kh_def refill_ready_kh_def
                         is_refill_sufficient_def is_refill_ready_def
                  split: if_splits option.splits
                   cong: conj_cong)
  by auto

lemma tcb_sched_context_update_None_valid_ep_q:
  "\<lbrace>valid_ep_q\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update caller None
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ep_q_def split:option.splits kernel_object.splits
                 dest!: get_tcb_SomeD)
  apply (drule_tac x=p in spec; clarsimp)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (intro conjI)
   apply (case_tac x3; clarsimp simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
   apply (clarsimp simp: active_sc_tcb_at_defs refill_sufficient_kh_def refill_ready_kh_def
                         is_refill_sufficient_def is_refill_ready_def
                  split: if_splits option.splits
                   cong: conj_cong)
  apply (safe; rule_tac x=scpa in exI; clarsimp)
  done

lemma tcb_sched_context_update_ko_at_Endpoint[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update from_tptr sc_opt
   \<lbrace>\<lambda>rv s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp get_object_wp
              simp: )
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

crunch ko_at_Endpoint[wp]: tcb_release_remove "\<lambda>s. Q (ko_at (Endpoint ep) p s)"

lemma set_sc_tcb_update_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>
     set_sc_obj_ref sc_tcb_update scp tcb
   \<lbrace>\<lambda>rv  s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (auto simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)
  by (rule_tac x=scpa in exI, clarsimp)

lemma set_sc_tcb_update_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_sc_obj_ref sc_tcb_update scp tcb \<lbrace>\<lambda>rv  s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: set_sc_obj_ref_def update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (auto simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
  by (rule_tac x=scpa in exI, clarsimp)

crunch valid_ep_q[wp]: tcb_sched_action, tcb_release_remove valid_ep_q

lemma reschedule_required_valid_ep_q:
  "\<lbrace>valid_ep_q\<rbrace>
     reschedule_required
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reschedule_required_def
  apply (wpsimp wp: tcb_sched_action_valid_ep_q thread_get_wp is_schedulable_wp)
  apply (clarsimp dest!: is_schedulable_opt_Some simp: pred_tcb_at_def obj_at_def is_tcb)
  done

lemma sched_context_donate_valid_ep_q_not_in_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. \<forall>ep epptr. ko_at (Endpoint ep) epptr s \<longrightarrow> caller \<notin> set (ep_queue ep))\<rbrace>
     sched_context_donate x2 caller
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: tcb_sched_context_update_valid_ep_q_not_in_q)
     apply (wpsimp wp: valid_ep_q_lift hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (wpsimp simp: test_reschedule_def
                    wp: hoare_vcg_all_lift hoare_vcg_imp_lift' reschedule_required_valid_ep_q)
       apply (wpsimp wp: tcb_sched_context_update_None_valid_ep_q hoare_vcg_imp_lift'
                         hoare_vcg_all_lift)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift hoare_vcg_if_lift2 get_sc_obj_ref_wp)+
  done

lemma reply_unlink_sc_no_ep_update[wp]:
  "reply_unlink_sc sp rp \<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) t s)\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  apply (wpsimp simp: set_sc_obj_ref_def
                  wp: hoare_vcg_imp_lift get_simple_ko_wp update_sched_context_wp
                      update_sk_obj_ref_wps set_simple_ko_wp)
  by (fastforce simp: obj_at_def split: if_splits)

lemma reply_remove_valid_ep_q:
  "\<lbrace>valid_ep_q
    and (\<lambda>s. \<forall>a. reply_tcb_reply_at (\<lambda>recv_opt. recv_opt = Some a) r s \<longrightarrow> st_tcb_at ((=) (BlockedOnReply r)) a s)
    and invs\<rbrace>
     reply_remove t r
   \<lbrace>\<lambda>_. valid_ep_q ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_remove_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: reply_unlink_tcb_valid_ep_q)
      apply (wpsimp wp: sched_context_donate_valid_ep_q_not_in_q hoare_vcg_imp_lift'
                        hoare_vcg_all_lift)
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' reply_unlink_sc_valid_ep_q
                       hoare_vcg_all_lift)
    apply clarsimp
    apply (wpsimp wp: gbn_wp)+
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "tcb_at t s")
   apply (clarsimp simp: obj_at_def is_tcb)
   apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>x y. st = BlockedOnReceive x y) t s
                      \<or> st_tcb_at (\<lambda>st. \<exists>x y. st = BlockedOnSend x y) t s")
    apply (fastforce simp: st_tcb_at_def obj_at_def reply_at_ppred_def)
   apply (subgoal_tac "(t, EPRecv) \<in> state_refs_of s xb \<or> (t, EPSend) \<in> state_refs_of s xb")
    apply (erule disjE)
     apply (drule sym_refsD, clarsimp)
     apply (clarsimp simp: state_refs_of_def get_refs_def tcb_st_refs_of_def pred_tcb_at_def obj_at_def
                    split: option.splits thread_state.splits if_splits)
    apply (drule sym_refsD, clarsimp)
    apply (clarsimp simp: state_refs_of_def get_refs_def tcb_st_refs_of_def pred_tcb_at_def obj_at_def
                   split: option.splits thread_state.splits if_splits)
   apply (case_tac xa;
          clarsimp simp: state_refs_of_def get_refs_def tcb_st_refs_of_def pred_tcb_at_def obj_at_def)
  apply (subgoal_tac "valid_reply reply s")
   apply (clarsimp simp: valid_reply_def)
  apply (erule valid_objs_valid_reply[rotated])
  apply (clarsimp)
  done

crunch cur_thread[wp]: reply_remove "\<lambda>s :: det_ext state. P (cur_thread s)"
  (wp: crunch_wps)

crunch not_in_release_q[wp]: reply_remove "\<lambda>s::det_state. not_in_release_q a s"
  (wp: crunch_wps tcb_release_remove_not_in_release_q')

lemma reply_unlink_tcb_ct_in_state:
  "\<lbrace>ct_in_state test and (\<lambda>s. \<forall>t. reply_tcb_reply_at ((=) (Some t)) r s \<longrightarrow> cur_thread s \<noteq> t)\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_. ct_in_state test ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp wp: sts_ctis_neq set_simple_ko_wp gts_wp get_simple_ko_wp)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def reply_at_ppred_def)
  done

lemma reply_remove_ct_in_state:
  "\<lbrace>ct_in_state test and (\<lambda>s. \<forall>t. reply_tcb_reply_at ((=) (Some t)) r s \<longrightarrow> cur_thread s \<noteq> t)\<rbrace>
     reply_remove t r
   \<lbrace>\<lambda>_. ct_in_state test ::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_remove_def
  apply (wpsimp wp: reply_unlink_tcb_ct_in_state)
  apply (wpsimp wp: ct_in_state_thread_state_lift sched_context_donate_cur_thread
                    hoare_vcg_imp_lift' hoare_vcg_all_lift get_simple_ko_wp)+
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma reply_remove_ct_active[wp]:
  "\<lbrace>(\<lambda>s. ct_active s \<or> ct_idle s)
    and (\<lambda>s. \<forall>t. reply_tcb_reply_at ((=) (Some t)) r s \<longrightarrow> cur_thread s \<noteq> t)\<rbrace>
     reply_remove t r
   \<lbrace>\<lambda>_ s::det_state. (ct_active s \<or> ct_idle s)\<rbrace>"
  unfolding reply_remove_def
  apply (wpsimp wp: hoare_vcg_disj_lift)
  apply (wpsimp wp: get_simple_ko_wp reply_unlink_tcb_ct_in_state
         | wpsimp wp: ct_in_state_thread_state_lift
                    hoare_vcg_imp_lift' hoare_vcg_all_lift)+
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma reply_remove_unbound_or_active_sc_tcb_at:
  "\<lbrace>(\<lambda>s. sym_refs (state_refs_of s))
    and tcb_at a
    and reply_tcb_reply_at (\<lambda>recv_opt. recv_opt = Some a) reply
    and valid_reply_scs\<rbrace>
   reply_remove caller reply
   \<lbrace>\<lambda>r s::det_state. bound_sc_tcb_at (\<lambda>a. a = None) a s \<or> active_sc_tcb_at a s\<rbrace>"
  unfolding reply_remove_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="(\<lambda>s. sym_refs (state_refs_of s)) and tcb_at a and reply_tcb_reply_at (\<lambda>recv_opt. recv_opt = Some a) reply and
                valid_reply_scs and (\<lambda>s. sc_with_reply reply s = r_sc_opt) and K(caller = a)" in hoare_weaken_pre[rotated])
   apply (clarsimp simp: reply_at_ppred_def obj_at_def)
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (case_tac "r_sc_opt"; simp)
   apply (wpsimp wp: reply_unlink_tcb_bound_sc_tcb_at reply_unlink_tcb_active_sc_tcb_at
                     hoare_vcg_disj_lift)
   apply (fastforce simp: valid_reply_scs_def )
  apply (clarsimp simp: bind_assoc)
  apply (wpsimp)
       apply (wpsimp wp: reply_unlink_tcb_bound_sc_tcb_at reply_unlink_tcb_active_sc_tcb_at
                         hoare_vcg_disj_lift)
      apply wpsimp
      apply (rule_tac Q="\<lambda>r. active_sc_tcb_at a" in hoare_strengthen_post[rotated], clarsimp)
      apply (wpsimp wp: sched_context_donate_active_sc_tcb_at_donate)
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' hoare_vcg_disj_lift)
    apply (wpsimp wp: gbn_wp)+
  apply (clarsimp simp: obj_at_def valid_reply_scs_def sc_with_reply_def reply_at_ppred_def is_tcb
                 dest!: the_pred_option_SomeD )
  apply (case_tac "tcb_sched_context tcb"; simp)
   apply (intro conjI impI)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (subgoal_tac "reply_sc_reply_at (\<lambda>x. x = (Some aa)) reply s")
     apply (fastforce simp: obj_at_def reply_at_ppred_def )
    apply (erule_tac list = "tl (sc_replies sc)" in  sym_refs_reply_sc_reply_at)
     apply (clarsimp simp: obj_at_def is_reply)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
    apply (fastforce intro: list.collapse)
   apply (intro disjI1)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (intro disjI2)
  apply (drule_tac x = a in spec)
  apply (fastforce simp: pred_tcb_at_def obj_at_def)
  done

lemma reply_at_ppred_eq_commute:
  "reply_at_ppred proj ((=) v) = reply_at_ppred proj (\<lambda>x. x = v)"
  by (intro ext) (auto simp: reply_at_ppred_def obj_at_def)

lemma transfer_caps_valid_machine_time[wp]:
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+
  done

crunches set_thread_state, thread_set, sched_context_update_consumed, reply_remove, as_user,
         set_message_info, copy_mrs, do_ipc_transfer, handle_fault_reply
  for valid_machine_time[wp]: "valid_machine_time::det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma ct_active_or_idle_simp:
  "(ct_active s \<or> ct_idle s) = ct_in_state (\<lambda>st. active st \<or> idle st) s"
  by (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def)

lemma do_reply_transfer_valid_sched:
  "\<lbrace>valid_sched and valid_ep_q and valid_reply_scs and valid_machine_time and
                invs and
                simple_sched_action and (\<lambda>s. ct_active s \<or> ct_idle s) and tcb_at sender\<rbrace>
     do_reply_transfer sender reply
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (case_tac recv_opt; clarsimp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac state)
  apply (case_tac state; clarsimp; (solves \<open>wpsimp\<close>)?)
  apply (wpsimp wp: possible_switch_to_valid_sched_strong)
               apply (wpsimp wp: handle_timeout_valid_sched)
              apply (wpsimp wp: postpone_valid_sched)
             apply (wpsimp)+
          apply (rule_tac Q="\<lambda>r. valid_ep_q and invs
                                 and st_tcb_at runnable a
                                 and bound_sc_tcb_at ((=) (Some sc_ptr)) a and active_sc_tcb_at a
                                 and scheduler_act_not a and not_queued a
                                 and not_in_release_q a and (ct_active or ct_idle)
                                 and valid_sched_except_blocked and  valid_blocked_except_set {a}"
                          in hoare_strengthen_post[rotated])
           apply (clarsimp simp: valid_sched_def pred_tcb_at_eq_commute cong: conj_cong)
           apply (subgoal_tac "sc_tcb_sc_at (\<lambda>p. p = Some a) sc_ptr s")
            apply (subgoal_tac "a \<noteq> idle_thread s")
             apply (case_tac fault; simp)
              apply (clarsimp, intro conjI impI; simp?)
               apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
               apply (clarsimp simp: valid_fault_def)
               apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
              apply (clarsimp simp: has_budget_equiv2 pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
             apply (clarsimp simp: has_budget_equiv2 pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
             apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
             apply (clarsimp simp: valid_fault_def)
            apply (fastforce dest!: st_tcb_at_idle_thread)
           apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric], simp, simp; clarsimp)
          apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                            refill_unblock_check_valid_ready_qs
                            refill_unblock_check_valid_release_q
                            refill_unblock_check_valid_sched_action
                            refill_unblock_check_ct_in_cur_domain
                            refill_unblock_check_st_tcb_at refill_unblock_check_invs
                            hoare_vcg_all_lift refill_unblock_check_active_sc_tcb_at
                            refill_unblock_check_valid_blocked_except_set
                            refill_unblock_check_invs refill_unblock_check_ct_in_state)
         apply wpsimp
        apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp )
       apply (wpsimp wp: gts_wp)
    (* key transition point *)
      apply (rule_tac Q="\<lambda>r. valid_sched_except_blocked and valid_machine_time and
                 (\<lambda>s. if (st_tcb_at runnable a s \<and> bound_sc_tcb_at bound a s) then
                         (valid_ep_q s \<and> invs s \<and> not_cur_thread a s \<and>
                 active_sc_tcb_at a s \<and>
                 scheduler_act_not a s \<and>
                 not_queued a s \<and>
                 not_in_release_q a s \<and> (ct_active s \<or> ct_idle s) \<and>
                 valid_blocked_except_set {a} s )
                 else valid_blocked s)"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp simp: valid_sched_def obj_at_def pred_tcb_at_def cong: conj_cong)
       apply (rule_tac x=tcb in exI)
       apply (clarsimp simp: valid_sched_def obj_at_def pred_tcb_at_def cong: conj_cong)
       apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
       apply (rename_tac ko; case_tac ko; clarsimp)
       apply (frule invs_sym_refs)
       apply (frule_tac tp=a in ARM.sym_ref_tcb_sc, simp+)
       apply (drule_tac tp=tp in ARM.sym_ref_tcb_sc)
         apply (simp+)[3]
      apply wpsimp+
        apply (wpsimp wp: hoare_vcg_imp_lift' sts_st_tcb_at_pred_False)
         apply (rule_tac Q="\<lambda>rv. (valid_sched_except_blocked and valid_blocked_except a)
               and (\<lambda>s. valid_ep_q s \<and>
                  invs s \<and>
                  not_cur_thread a s \<and>
                  active_sc_tcb_at a s \<and>
                  scheduler_act_not a s \<and>
                  not_queued a s \<and>
                  not_in_release_q a s \<and>
                  (ct_active s \<or> ct_idle s) \<and> valid_machine_time s)"
                         in hoare_strengthen_post[rotated])
          apply clarsimp
         apply (wpsimp wp: set_thread_state_break_valid_sched set_thread_state_valid_ep_q
                           sts_invs_minor2 sts_ctis_neq hoare_vcg_disj_lift )
        apply (wpsimp wp: hoare_vcg_imp_lift' set_thread_state_bound_sc_tcb_at sts_st_tcb_at')
        apply (rule_tac Q="\<lambda>rv. valid_sched and valid_machine_time "
                        in hoare_strengthen_post[rotated])
         apply (clarsimp simp: valid_sched_def)
        apply (wpsimp wp: set_thread_state_runnable_valid_sched2)
       apply (wpsimp wp: hoare_vcg_imp_lift' do_ipc_transfer_cur_thread hoare_vcg_disj_lift
                         ct_in_state_thread_state_lift)
      apply (wpsimp wp: )
           apply (intro conjI impI)
            apply (wpsimp wp: hoare_vcg_imp_lift' sts_st_tcb_at_pred_False)
             apply (rule_tac Q="\<lambda>rv. (valid_sched_except_blocked and valid_blocked_except x)
                   and (\<lambda>s. valid_ep_q s \<and>
                      invs s \<and>
                      not_cur_thread x s \<and>
                      active_sc_tcb_at x s \<and>
                      scheduler_act_not x s \<and>
                      not_queued x s \<and>
                      not_in_release_q x s \<and>
                      (ct_active s \<or> ct_idle s) \<and> valid_machine_time s)"
                             in hoare_strengthen_post[rotated])
              apply clarsimp
             apply (wpsimp wp: set_thread_state_break_valid_sched set_thread_state_valid_ep_q
                               sts_invs_minor2 sts_ctis_neq hoare_vcg_disj_lift )
            apply (wpsimp wp: hoare_vcg_imp_lift' sts_st_tcb_at')
            apply (rule_tac Q="\<lambda>rv. (valid_sched and valid_machine_time)"
                            in hoare_strengthen_post[rotated])
             apply (clarsimp simp: valid_sched_def)
            apply (wpsimp wp: set_thread_state_runnable_valid_sched2)
           apply (wpsimp wp: hoare_vcg_imp_lift' sts_st_tcb_at_pred_False)
            apply (rule_tac Q="\<lambda>rv. (valid_sched)
                  and (\<lambda>s. valid_ep_q s \<and>
                     invs s \<and>
                     not_cur_thread x s \<and>
                     active_sc_tcb_at x s \<and>
                     scheduler_act_not x s \<and>
                     not_queued x s \<and>
                     not_in_release_q x s \<and>
                     (ct_active s \<or> ct_idle s) \<and>
                     valid_machine_time s)"
                            in hoare_strengthen_post[rotated])
             apply (clarsimp simp: valid_sched_def)
            apply (wpsimp wp: set_thread_state_sched_act_not_valid_sched set_thread_state_valid_ep_q
                              sts_invs_minor2 sts_ctis_neq hoare_vcg_disj_lift )
           apply (wpsimp wp: hoare_vcg_imp_lift' sts_st_tcb_at')
           apply (rule_tac Q="\<lambda>rv. (valid_sched and valid_machine_time)"
                           in hoare_strengthen_post[rotated])
            apply (clarsimp simp: valid_sched_def)
           apply (wpsimp wp: set_thread_state_sched_act_not_valid_sched)
          apply clarsimp
          apply (rule_tac Q="\<lambda>rv. (valid_sched)
                and (valid_ep_q and invs and  simple_sched_action and valid_machine_time and
                   st_tcb_at (\<lambda>st. st = Inactive) x and
                   not_queued x and not_in_release_q x and (\<lambda>s. cur_thread s \<noteq> x) and
                   ex_nonz_cap_to x and (\<lambda>s. x \<noteq> idle_thread s) and
                   fault_tcb_at ((=) None) x and
                   (\<lambda>s. bound_sc_tcb_at (\<lambda>a. a = None) x s \<or> active_sc_tcb_at x s) and
                   (ct_active or ct_idle))"
                          in hoare_strengthen_post[rotated])
           apply (clarsimp simp: valid_sched_def)
           apply (intro conjI)
             apply (clarsimp simp: pred_tcb_at_def obj_at_def)
            apply (clarsimp simp: pred_tcb_at_def obj_at_def not_cur_thread_def)
           apply (clarsimp simp: bound_sc_tcb_at_def active_sc_tcb_at_def obj_at_def)
          apply (wpsimp wp: thread_set_not_state_valid_sched thread_set_no_change_tcb_state
                            thread_set_cap_to)
           apply (clarsimp simp: ran_def tcb_cap_cases_def split: if_splits)
          apply (wpsimp wp: hoare_vcg_disj_lift thread_set_no_change_tcb_sched_context
                            thread_set_active_sc_tcb_at thread_set_ct_in_state
                            thread_set_pred_tcb_at_sets_true)
         apply (wpsimp wp: handle_fault_reply_valid_sched hoare_vcg_disj_lift
                           ct_in_state_thread_state_lift)
        apply (wpsimp wp: thread_get_wp)+
    apply (rule_tac Q="\<lambda>rv. (valid_sched) and valid_ep_q and invs and simple_sched_action and
                            (\<lambda>s. st_tcb_at inactive a s \<and>
                           not_queued a s \<and> (ct_active s \<or> ct_idle s) \<and> valid_machine_time s \<and>
                           not_in_release_q a s \<and>
                           cur_thread s \<noteq> a \<and> tcb_at sender s \<and>
                           ex_nonz_cap_to a s \<and>
                           a \<noteq> idle_thread s \<and> ((bound_sc_tcb_at (\<lambda>a. a = None) a s \<or>
                          active_sc_tcb_at a s)))"
                    in hoare_strengthen_post[rotated])
     apply (clarsimp simp: valid_sched_def obj_at_def pred_tcb_at_def is_tcb)
     apply (safe;
            clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def not_cur_thread_def)
    apply (wpsimp wp: reply_remove_valid_sched reply_remove_valid_ep_q reply_remove_invs
                      reply_remove_unbound_or_active_sc_tcb_at)
   apply wpsimp
  apply (clarsimp simp: pred_tcb_at_eq_commute reply_at_ppred_eq_commute)
  apply (subgoal_tac "cur_thread s \<noteq> a")
   apply (intro conjI impI)
              apply (clarsimp simp: reply_at_ppred_def obj_at_def pred_tcb_at_def)
             apply (clarsimp simp: reply_at_ppred_def obj_at_def pred_tcb_at_def)
            apply fastforce
           apply (fastforce dest!: valid_sched_not_runnable_not_inq simp: pred_tcb_at_def obj_at_def)
          apply clarsimp
         apply (clarsimp simp: reply_at_ppred_def obj_at_def pred_tcb_at_def)
        apply (fastforce dest!: valid_sched_not_runnable_not_inq simp: pred_tcb_at_def obj_at_def)
       apply clarsimp
      apply (clarsimp elim!: st_tcb_ex_cap')
     apply (fastforce dest!: st_tcb_at_idle_thread)
    apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def is_tcb)+
  done

lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and not_queued thread and not_in_release_q thread
      and scheduler_act_not thread and invs and (\<lambda>_. valid_fault ex)
      and valid_ep_q and (ct_active or ct_idle)
      and active_sc_tcb_at thread and budget_ready thread and budget_sufficient thread\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_fault_def unless_def
  by (wpsimp wp: handle_no_fault_valid_sched send_fault_ipc_valid_sched hoare_vcg_if_lift2
                 send_fault_ipc_not_queued send_fault_ipc_not_in_release_q
                 send_fault_ipc_scheduler_act_not hoare_drop_imps hoare_vcg_conj_lift)

end

lemma idle_not_queued'':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s); queue \<times> {rt} \<subseteq> state_refs_of s ptr\<rbrakk> \<Longrightarrow>
     idle_thread s \<in> queue \<longrightarrow> ptr = idle_sc_ptr"
  by (frule idle_only_sc_refs)
     (fastforce simp: valid_idle_def sym_refs_def pred_tcb_at_def obj_at_def state_refs_of_def
                split: option.splits)


context DetSchedSchedule_AI begin
(*
crunches transfer_caps_loop, transfer_caps
for active_sc_tcb_at: "active_sc_tcb_at t"
  (wp: transfer_caps_loop_pres mapM_wp' maybeM_wp hoare_drop_imps simp: Let_def)

crunches copy_mrs,make_fault_msg
for active_sc_tcb_at[wp]: "active_sc_tcb_at t"
  (wp: transfer_caps_loop_pres hoare_drop_imps select_wp mapM_wp simp: unless_def if_fun_split)

crunches send_ipc
for active_sc_tcb_at: "active_sc_tcb_at t"
  (wp: transfer_caps_loop_pres hoare_drop_imps select_wp mapM_wp maybeM_wp
simp: unless_def if_fun_split
ignore: make_arch_fault_msg possible_switch_to copy_mrs)
*)

(* do we need this?
lemma send_ipc_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
     send_ipc block call badge can_grant can_donate thread epptr \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp)
    apply (wpsimp+)[2]
  apply (rename_tac queue)
  apply (case_tac queue; clarsimp)
  apply wpsimp
*)

lemmas update_sc_replies_active_sc_tcb_at[wp] =
       active_sc_tcb_at_update_sched_context_no_change[where f = "sc_replies_update g" for g]

lemma reply_remove_tcb_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t \<rbrace>
     reply_remove_tcb tptr rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply (wpsimp wp: get_sk_obj_ref_wp)
  done

crunches cancel_ipc
  for active_sc_tcb_at: "active_sc_tcb_at t::det_state \<Rightarrow> _"
  (wp: hoare_drop_imp crunch_wps)

lemma set_thread_state_st_tcb_at:
  " P ts \<Longrightarrow>
    \<lbrace>st_tcb_at \<top> tcbptr\<rbrace>
      set_thread_state tcbptr ts
    \<lbrace>\<lambda>rv s. st_tcb_at P tcbptr s\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: is_schedulable_wp set_object_wp)
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

lemma set_thread_state_budget_conditions:
  "\<lbrace>\<lambda>s. not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>
     set_thread_state tcbptr Running
   \<lbrace>\<lambda>rv s. not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: is_schedulable_wp set_object_wp set_scheduler_action_wp)
  apply (subgoal_tac "not_in_release_q tcbptr s \<longrightarrow>
         budget_ready tcbptr (s\<lparr>kheap := kheap s(tcbptr \<mapsto> TCB (y\<lparr>tcb_state := Running\<rparr>))\<rparr>) \<and>
         budget_sufficient tcbptr (s\<lparr>kheap := kheap s(tcbptr \<mapsto> TCB (y\<lparr>tcb_state := Running\<rparr>))\<rparr>)")
   apply (intro allI impI conjI; fastforce)
  apply (intro allI impI)
  apply (subgoal_tac "budget_ready tcbptr s \<and> budget_sufficient tcbptr s")
   apply (intro conjI;
          clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def;
          rule_tac x="scpa" in exI; simp)
    using get_tcb_SomeD
    apply fastforce+
  done

lemma tcb_sched_context_update_active_sc_tcb_at:
  "\<lbrace>test_sc_refill_max sc_ptr::det_state \<Rightarrow> _\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr)
   \<lbrace>\<lambda>r. active_sc_tcb_at tcb_ptr\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                        test_sc_refill_max_def)
  using get_tcb_SomeD by fastforce

crunch active_sc_tcb_at[wp]: postpone "\<lambda>s :: det_state. Q (active_sc_tcb_at t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma sched_context_resume_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at tptr\<rbrace>
     sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>r. active_sc_tcb_at tptr :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: thread_get_wp is_schedulable_wp refill_sufficient_wp refill_ready_wp)
  apply (fastforce simp: obj_at_def is_schedulable_opt_def is_tcb
                  split: option.splits
                  dest!: get_tcb_SomeD)
  done

lemma as_user_has_budget[wp]:
  "\<lbrace>has_budget tcb_ptr\<rbrace> as_user ptr s \<lbrace>\<lambda>_. has_budget tcb_ptr\<rbrace>"
  by (wpsimp wp: as_user_budget_ready as_user_budget_sufficient
                 as_user_active_sc_tcb_at as_user_pred_tcb_at hoare_vcg_disj_lift
           simp: has_budget_def)

lemma tcb_sched_context_update_has_budget:
  "\<lbrace>test_sc_refill_max scp and is_refill_sufficient scp 0 and is_refill_ready scp 0\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
   \<lbrace>\<lambda>r. has_budget tptr\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp: has_budget_equiv)
  apply (intro conjI)
   apply (clarsimp simp: tcb_at_def get_tcb_def)
  apply (intro impI conjI)
    apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def)
    apply (simp only: obj_at_def)
    apply auto
    apply (simp only: test_sc_refill_max_def)
    apply clarsimp
   apply (clarsimp simp:  pred_tcb_at_def)
   apply (simp only: obj_at_def)
   apply auto
   apply (simp only: is_refill_sufficient_def obj_at_def)
   apply clarsimp
  apply (clarsimp simp:  pred_tcb_at_def)
  apply (simp only: obj_at_def)
  apply auto
  apply (simp only: is_refill_ready_def obj_at_def)
  apply clarsimp
  done

lemma sched_context_donate_has_budget:
  "\<lbrace>\<lambda>s. test_sc_refill_max scp s \<and> is_refill_sufficient scp 0 s \<and> is_refill_ready scp 0 s \<and>
        sc_tcb_sc_at (\<lambda>t. t = None) scp s\<rbrace>
   sched_context_donate scp tcbp
   \<lbrace>\<lambda>r. has_budget tcbp :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: tcb_sched_context_update_has_budget set_sc_refills_is_refill_ready_indep
                    set_sc_refills_is_refill_sufficient_indep test_reschedule_case
              simp: get_sc_obj_ref_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma refill_unblock_check_has_budget:
  "\<lbrace>has_budget tptr and bound_sc_tcb_at ((=) (Some sc_ptr)) tptr and valid_machine_time\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>r. has_budget tptr :: det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp refill_ready_wp)
  apply (clarsimp simp: has_budget_equiv)
  apply (intro conjI impI)
     apply (clarsimp simp: obj_at_def is_tcb)
    apply (fastforce simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                          active_sc_tcb_at_def test_sc_refill_max_def)
   apply (subgoal_tac "sufficient_refills 0 (refills_merge_prefix (refill_hd sca\<lparr>r_time := cur_time s\<rparr> # tl (sc_refills sca)))")
    apply (fastforce simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                          active_sc_tcb_at_def is_refill_sufficient_def)
   apply (clarsimp simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                         active_sc_tcb_at_def is_refill_ready_def)
   apply (safe; clarsimp simp: is_refill_sufficient_def obj_at_def sufficient_refills_def refills_capacity_def)
  subgoal sorry \<comment> \<open>refills_merge_prefix results in at least MIN_BUDGET in head\<close>
  apply (clarsimp simp: is_refill_ready_def bound_sc_tcb_at_def obj_at_def)
  apply (clarsimp simp: r_time_hd_refills_merge_prefix)
  apply (intro conjI impI)
   apply force
  apply simp+
  apply (erule cur_time_no_overflow)
  done

lemma sched_context_donate_bound_sc_tcb_at:
  "\<lbrace>\<top>\<rbrace> sched_context_donate scp tptr \<lbrace>\<lambda>rv. bound_sc_tcb_at ((=) (Some scp)) tptr\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: ssc_bound_tcb_at')

lemma sched_context_donate_sc_tcb_sc_at:
  "\<lbrace>\<top>\<rbrace> sched_context_donate scp tptr \<lbrace>\<lambda>rv. sc_tcb_sc_at ((=) (Some tptr)) scp\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: sc_tcb_update_sc_tcb_sc_at)

lemma st_in_waitingntfn':
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_objs s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> t\<in>set q
   \<Longrightarrow> st_tcb_at (\<lambda>x. x = BlockedOnNotification ntfnptr) t s"
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule_tac x = t in ballE)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfnptr in allE)
   apply (erule_tac x = "(t, NTFNSignal)" in ballE)
    apply (auto simp: state_refs_of_def is_tcb obj_at_def pred_tcb_at_def tcb_st_refs_of_def
                      get_refs_def2
               split: thread_state.splits if_splits)
  done

lemma maybe_donate_sc_ct_not_in_q2:
  "\<lbrace> ct_not_in_q \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma set_object_simple_ko_has_budget:
  "\<lbrace>has_budget t and obj_at is_simple_type ptr and K (is_simple_type newko)\<rbrace>
     set_object ptr newko
   \<lbrace>\<lambda>_. has_budget t\<rbrace>"
  unfolding set_object_def
  apply (wpsimp simp: set_object_def get_object_def has_budget_equiv)
  apply (intro conjI impI)
     apply (clarsimp simp: obj_at_def is_tcb)
    apply (clarsimp simp: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def test_sc_refill_max_def)
    apply fastforce
   apply (clarsimp simp:  bound_sc_tcb_at_def obj_at_def is_refill_sufficient_def )
   apply fastforce
  apply (clarsimp simp:  bound_sc_tcb_at_def obj_at_def is_refill_ready_def)
  apply fastforce
  done

lemma set_simple_ko_has_budget[wp]:
  "\<lbrace>has_budget t\<rbrace>
     set_simple_ko f ptr ep
   \<lbrace>\<lambda>_. has_budget t\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_simple_ko_has_budget get_object_wp)
  apply (clarsimp simp: obj_at_def split: option.splits)
  done

lemma has_budget_update_ntfn:
  "ntfn_at ptr2 s \<Longrightarrow>
   has_budget ptr1 (s\<lparr>kheap := \<lambda>a. if a = ptr2 then Some (Notification n) else kheap s a\<rparr>)
   = has_budget ptr1 s"
  apply (clarsimp simp: has_budget_def)
  apply (rule disj_cong)
   apply (clarsimp simp: bound_sc_tcb_at_def obj_at_def is_ntfn)
  apply (rule conj_cong)
   apply (clarsimp simp: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def test_sc_refill_max_def
                         is_ntfn
                  split: option.splits)
   apply fastforce
  apply (rule conj_cong)
   apply (clarsimp simp: is_refill_sufficient_def bound_sc_tcb_at_def obj_at_def is_ntfn
                         sufficient_refills_def
                  split: option.splits)
   apply (intro iffI; safe; simp)
   apply (rule_tac x = scp in exI)
   apply fastforce
  apply (clarsimp simp: is_refill_ready_def bound_sc_tcb_at_def obj_at_def is_ntfn
                 split: option.splits)
  apply (intro iffI; safe; simp)
  apply (rule_tac x = scp in exI)
  apply fastforce
  done

lemma maybe_donate_sc_cond_has_budget:
  "\<lbrace>has_budget tcbptr and st_tcb_at runnable tcbptr\<rbrace>
     maybe_donate_sc tcbptr ntfnptr
   \<lbrace>\<lambda>rv s. active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> has_budget tcbptr s\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_cond_has_budget refill_unblock_check_ko_at_SchedContext
                     sched_context_donate_sc_tcb_sc_at sched_context_donate_bound_sc_tcb_at
                simp: get_sc_obj_ref_def)
  apply wpsimp
  done

lemma send_signal_WaitingNtfn_helper:
  notes not_not_in_eq_in[iff] shows
  "ntfn_obj ntfn = WaitingNtfn wnlist \<Longrightarrow>
   \<lbrace>ko_at (Notification ntfn) ntfnptr and
    st_tcb_at ((=) (BlockedOnNotification ntfnptr)) (hd wnlist) and
    valid_ntfn_q and valid_sched and invs and valid_machine_time\<rbrace>
   update_waiting_ntfn ntfnptr wnlist (ntfn_bound_tcb ntfn) (ntfn_sc ntfn) badge
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wpsimp wp: possible_switch_to_valid_sched_strong)
          apply (wpsimp wp: is_schedulable_wp)+
        apply (rename_tac tcbptr x)
        apply (rule_tac Q="\<lambda>r s. tcbptr \<noteq> idle_thread s \<and> st_tcb_at runnable tcbptr s \<and>
                                 valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s \<and>
        (active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> has_budget tcbptr s)" in hoare_strengthen_post[rotated])
         apply (clarsimp simp: obj_at_def valid_sched_def
                        split: option.splits dest!: get_tcb_SomeD)
             apply (clarsimp dest!: schedulable_unfold2 st_tcb_at_tcb_at)
         apply (intro conjI; intro allI impI)
          apply (intro conjI; intro allI impI)
           apply (clarsimp simp: not_in_release_q_def has_budget_def active_sc_tcb_at_defs)
          apply (erule valid_blocked_divided2)
          apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                                runnable_eq_active)
         apply (erule valid_blocked_divided2)
         apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                               active_sc_tcb_at_defs)
        apply (wpsimp wp: maybe_donate_sc_valid_ready_qs
                          maybe_donate_sc_valid_release_q
                          maybe_donate_sc_valid_sched_action
                          maybe_donate_sc_ct_not_in_q2
                          maybe_donate_sc_ct_in_cur_domain
                          maybe_donate_sc_valid_blocked_except_set maybe_donate_sc_cond_has_budget)
       apply wpsimp
      apply (rule_tac Q="\<lambda>_ s. (valid_sched_except_blocked s \<and> valid_blocked_except_set {x1} s)
                         \<and>
                  not_queued x1 s \<and>
                  x1 \<noteq> idle_thread s \<and>
                  sym_refs (state_refs_of s) \<and>
                  not_cur_thread x1 s \<and> valid_objs s \<and>
                  st_tcb_at runnable x1 s \<and> valid_machine_time s \<and> scheduler_act_not x1 s \<and> not_in_release_q x1 s \<and>
                  has_budget x1 s"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp)
      apply (rule hoare_vcg_conj_lift)
       apply (rule set_thread_state_break_valid_sched[simplified pred_conj_def])
      apply (wpsimp wp: sts_st_tcb_at')
     apply simp
     apply (wpsimp wp: set_simple_ko_valid_sched set_simple_ko_wp)
    apply wpsimp+
  apply (intro conjI)
      apply (erule valid_sched_not_runnable_not_queued)
      apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
     apply (fastforce dest: st_tcb_at_idle_thread)
   defer
     apply (rule valid_nftn_qD2; assumption?)
     apply fastforce defer
    apply (erule valid_sched_not_runnable_scheduler_act_not)
    apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
   apply (erule valid_sched_not_runnable_not_in_release_q)
   apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
  apply (subst has_budget_update_ntfn;
         clarsimp simp: obj_at_def ntfn_at_pred_def is_ntfn_def)
  apply (rule valid_nftn_qD1; assumption?)
   apply (clarsimp simp: obj_at_def, assumption)
  apply fastforce
(* sym_refs *)
   apply (case_tac wnlist; clarsimp)
   apply (frule invs_valid_objs)
   apply (drule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (drule invs_sym_refs)
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_splits)
     apply (intro conjI impI; fastforce simp: obj_at_def state_refs_of_def get_refs_def2 ntfn_q_refs_of_def
      dest!: symreftype_inverse'
      split: option.splits list.splits if_splits)+
   apply (clarsimp split: if_splits simp: pred_tcb_at_def obj_at_def)
    apply (intro conjI impI; clarsimp simp: tcb_st_refs_of_def state_refs_of_def
      split: option.splits if_splits list.splits thread_state.splits dest!: symreftype_inverse')
           apply (clarsimp simp: get_refs_def2)+
   apply (intro conjI impI; fastforce simp: is_tcb obj_at_def state_refs_of_def get_refs_def2 ntfn_q_refs_of_def
      dest!: symreftype_inverse'
      split: option.splits list.splits if_splits)
   (* valid_objs *)
  apply (case_tac wnlist; clarsimp)
  apply (drule invs_valid_objs)
  apply (clarsimp simp: valid_objs_def obj_at_def pred_tcb_at_def split: if_split_asm)
  (* ptr = ntfnptr *)
   apply (drule_tac x=ntfnptr in bspec, clarsimp+)
   apply (fastforce simp: valid_obj_def valid_ntfn_def valid_bound_obj_def obj_at_def is_tcb is_sc_obj_def
      split: list.splits option.splits)
   (* ptr \<noteq> ntfnptr *)
  apply (frule_tac x=ntfnptr in bspec, clarsimp+)
  apply (drule_tac x=ptr in bspec, clarsimp+)
  apply (simp only: fun_upd_apply[symmetric])
  apply (rule valid_obj_same_type, simp)
  by (clarsimp simp: valid_obj_def valid_ntfn_def split: list.splits option.splits) simp+

lemma set_thread_state_not_runnable':
  "\<lbrace>st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr1\<rbrace>
     set_thread_state tcbptr2 Inactive
   \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr1\<rbrace>"
  apply (wpsimp simp: set_thread_state_def
                  wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma set_thread_state_not_runnable[wp]:
  "\<lbrace>tcb_at tcbptr\<rbrace>
     set_thread_state tcbptr Inactive
   \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr\<rbrace>"
  apply (wpsimp simp: set_thread_state_def
                  wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma cancel_signal_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr\<rbrace>
      cancel_signal tcbptr ntfnptr
   \<lbrace>\<lambda>rv s. valid_sched (s :: det_state)\<rbrace>"
  unfolding cancel_signal_def
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched
                    set_object_wp get_simple_ko_wp set_simple_ko_valid_sched)
  using valid_sched_not_runnable_scheduler_act_not
  apply (fastforce simp: st_tcb_at_def obj_at_def)
  done

lemma blocked_cancel_ipc_BOR_valid_sched':
  "\<lbrace>valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv s. valid_sched (s :: det_state)\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def get_blocking_object_def thread_get_def
                  wp: set_thread_state_not_runnable_valid_sched set_simple_ko_valid_sched
                      reply_unlink_tcb_valid_sched get_simple_ko_wp)
        apply (rule_tac Q="\<lambda>r s. valid_sched s \<and> scheduler_act_not tcbptr s \<and>
                           st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr s" in hoare_strengthen_post[rotated])
         apply (clarsimp)
        apply (wpsimp simp: get_blocking_object_def wp: get_simple_ko_wp)+
  apply (clarsimp simp: scheduler_act_not_def valid_sched_def valid_sched_action_def
                        weak_valid_sched_action_2_def st_tcb_at_def obj_at_def)
  done

lemma cancel_ipc_BOR_valid_sched:
  "\<lbrace>(st_tcb_at ((=) (BlockedOnReceive tptr reply)) tcbptr) and valid_sched\<rbrace>
      cancel_ipc tcbptr
   \<lbrace>\<lambda>rv s. valid_sched (s :: det_state)\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state; clarsimp)
         apply ((wpsimp wp: thread_set_not_state_valid_sched)+)[3]
      apply (wpsimp wp: blocked_cancel_ipc_BOR_valid_sched' thread_set_not_state_valid_sched
                        thread_set_no_change_tcb_pred)
     apply (clarsimp simp: st_tcb_at_def obj_at_def
            | rule_tac Q="\<bottom>" in hoare_weaken_pre
            | case_tac "tcb_state tcb")+
  done

lemma blocked_cancel_ipc_BOR_st_tcb_at_not_runnable[wp]:
  "\<lbrace>tcb_at tcbptr\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr s\<rbrace>"
  unfolding blocked_cancel_ipc_def
  by (wpsimp wp: hoare_drop_imps)

lemma valid_ep_remove1_SendEP:
  "valid_ep (SendEP q) s \<Longrightarrow> valid_ep (case remove1 tp q of
                                              [] \<Rightarrow> IdleEP
                                      | a # list \<Rightarrow> update_ep_queue (SendEP q) (remove1 tp q)) s"
  apply (clarsimp simp: valid_ep_def)
  apply (case_tac "remove1 tp q"; simp)
  apply (subgoal_tac "set (remove1 tp q) \<subseteq> set q")
   apply (subgoal_tac "distinct (remove1 tp q)")
    apply (intro allI impI conjI; clarsimp?)
    apply fastforce
   apply (rule distinct_remove1, clarsimp)
  apply (rule set_remove1_subset)
  done

lemma valid_ep_remove1_RecvEP:
  "valid_ep (RecvEP q) s \<Longrightarrow> valid_ep (case remove1 tp q of
                                              [] \<Rightarrow> IdleEP
                                      | a # list \<Rightarrow> update_ep_queue (RecvEP q) (remove1 tp q)) s"
  apply (clarsimp simp: valid_ep_def)
  apply (case_tac "remove1 tp q"; simp)
  apply (subgoal_tac "set (remove1 tp q) \<subseteq> set q")
   apply (subgoal_tac "distinct (remove1 tp q)")
    apply (intro allI impI conjI; clarsimp?)
    apply fastforce
   apply (rule distinct_remove1, clarsimp)
  apply (rule set_remove1_subset)
  done

lemma valid_objs_ep_update:
  "\<lbrakk>ep_at epptr s; valid_ep ep s; valid_objs s\<rbrakk> \<Longrightarrow> valid_objs (s\<lparr>kheap := kheap s(epptr \<mapsto> Endpoint ep)\<rparr>)"
  apply (clarsimp simp: valid_objs_def dom_def
                 elim!: obj_atE)
  apply (intro conjI impI)
   apply (rule valid_obj_same_type)
      apply (simp add: valid_obj_def)+
   apply (clarsimp simp: a_type_def is_ep)
  apply clarsimp
  apply (rule valid_obj_same_type)
     apply (drule_tac x=ptr in spec, simp)
    apply (simp add: valid_obj_def)
   apply assumption
  apply (clarsimp simp add: a_type_def is_ep)
  done

lemma valid_ep_valid_objs:
  "\<lbrakk>valid_objs s; kheap s ptr = Some (Endpoint k)\<rbrakk> \<Longrightarrow> valid_ep k s"
  by (clarsimp simp: valid_objs_def valid_obj_def; force)

crunch weak_budget_conditions[wp]: set_scheduler_action "\<lambda>s. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)"
  (simp:  )

lemma set_thread_state_weak_budget_conditions[wp]:
  "set_thread_state a b \<lbrace>\<lambda>s::det_state. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def split: option.splits)
  apply (case_tac "tcbptr \<noteq> a"; (simp add: )?)
  using get_tcb_SomeD apply (intro conjI; rule_tac x=scpa in exI; fastforce)+
  done

lemma reply_unlink_tcb_weak_budget_conditions[wp]:
  "\<lbrace>(\<lambda>s::det_state. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)) and valid_objs \<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>rv s::det_state. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp simp: get_thread_state_def update_sk_obj_ref_def
                  wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp)
  apply (clarsimp simp: test_sc_refill_max_def obj_at_def reply_at_pred_def
                 split: option.splits)
  apply (erule (1) pspace_valid_objsE,
         clarsimp simp: valid_obj_def valid_reply_def tcb_at_def
                 dest!: get_tcb_SomeD)
  apply (intro conjI allI impI;
         clarsimp simp: pred_tcb_at_def is_refill_ready_def obj_at_def is_refill_sufficient_def
                        in_release_queue_def not_in_release_q_def)
     apply (intro conjI allI impI | fastforce | rule_tac x=scpa in exI)+
 done

lemma budget_sufficient_update_kheap:
  "t \<noteq> p \<Longrightarrow> obj_at (Not \<circ> is_SchedContext) p s \<Longrightarrow> budget_sufficient t s \<Longrightarrow> budget_sufficient t (s\<lparr>kheap := kheap s(p \<mapsto> ko)\<rparr>)"
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)

lemma budget_ready_update_kheap:
  "t \<noteq> p \<Longrightarrow> obj_at (Not \<circ> is_SchedContext) p s \<Longrightarrow> budget_ready t s \<Longrightarrow> budget_ready t (s\<lparr>kheap := kheap s(p \<mapsto> ko)\<rparr>)"
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_ready_def)

(* FIXME: is_TCB etc. now provided by datatype package - get rid of all is_tcb and similar *)
lemma is_tcb_is_TCB:
  "is_tcb = is_TCB"
  by (rule ext, clarsimp simp: is_tcb_def split: kernel_object.split)

lemma blocked_cancel_ipc_BOR_weak_budget_conditions:
  "\<lbrace>budget_sufficient tcbptr and valid_objs\<rbrace>
   blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv s::det_state. (budget_sufficient tcbptr s)\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def
                  wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp
                      get_ep_queue_wp get_blocking_object_wp)
  by (safe;
      subst budget_sufficient_update_kheap;
      fastforce dest!: pred_tcb_at_tcb_at simp: obj_at_def is_tcb_is_TCB)

lemma blocked_cancel_ipc_BOR_weak_budget_conditions':
  "\<lbrace>(\<lambda>s. budget_ready tcbptr s) and valid_objs\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv s::det_state. (budget_ready tcbptr s)\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def
                  wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp
                      get_ep_queue_wp get_blocking_object_wp)
  by (safe;
      subst budget_ready_update_kheap;
      fastforce dest!: pred_tcb_at_tcb_at simp: obj_at_def is_tcb_is_TCB)

lemma blocked_cancel_ipc_BOR_has_budget:
  "\<lbrace>has_budget tcbptr and valid_objs\<rbrace>
   blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv s :: det_state. (has_budget tcbptr s)\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def has_budget_def
                  wp: thread_get_wp get_simple_ko_wp
                      get_ep_queue_wp get_blocking_object_wp hoare_vcg_disj_lift
                      hoare_drop_imps hoare_vcg_all_lift)
  done

lemma cancel_ipc_BOR_other:
  "\<lbrace>(st_tcb_at ((=) (BlockedOnReceive tptr reply)) tcbptr) and invs and
        (\<lambda>s. has_budget tcbptr s)\<rbrace>
      cancel_ipc tcbptr
   \<lbrace>\<lambda>rv s::det_state. has_budget tcbptr s\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state; clarsimp)
         prefer 4
         apply (wpsimp wp: thread_set_valid_objs
                           blocked_cancel_ipc_BOR_has_budget
                     simp: valid_tcb_def ran_tcb_cap_cases)
        apply (rule hoare_weaken_pre,
               rule hoare_pre_cont
               | clarsimp simp: st_tcb_at_def obj_at_def
               | case_tac "tcb_state tcb")+
  done

lemma valid_eq_q_Blocked_on_Receive_has_budget:
  "invs s \<Longrightarrow> valid_ep_q s \<Longrightarrow> st_tcb_at ((=) (BlockedOnReceive a b)) tcbptr s
   \<Longrightarrow> has_budget tcbptr s"
  apply (simp only: pred_tcb_at_eq_commute)
  apply (subgoal_tac "(tcbptr, EPRecv) \<in> state_refs_of s a")
   apply (subgoal_tac "ep_at a s")
    apply (clarsimp simp: state_refs_of_def refs_of_def obj_at_def is_ep ep_q_refs_of_def
                   split: option.splits)
    apply (case_tac ep; simp)
    apply (subgoal_tac "tcbptr\<in>set (ep_queue ep)")
     apply (clarsimp simp: valid_ep_q_def
                    split: option.splits)
     apply (simp only: has_budget_def)
     apply fastforce
    apply (clarsimp simp: ep_queue_def)
   apply (clarsimp simp: state_refs_of_def obj_at_def split: option.splits)
   apply (case_tac x2)
         apply (clarsimp simp: refs_of_def get_refs_def is_ep_def split: option.splits)+
  apply (erule sym_refsE[OF invs_sym_refs])
  apply (clarsimp simp: state_refs_of_def obj_at_def pred_tcb_at_def get_refs_def
                 split: option.splits)
  done

crunches cancel_ipc
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma sts_cancel_ipc_Running_invs:
  "\<lbrace>st_tcb_at ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState)  t
        and invs and ex_nonz_cap_to t and fault_tcb_at ((=) None) t\<rbrace>
    set_thread_state t Structures_A.Running
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wp sts_invs_minor2)
  apply clarsimp
  apply (auto elim!: pred_tcb_weakenE
           notE [rotated, OF _ idle_no_ex_cap]
           simp: invs_def valid_state_def valid_pspace_def)
  done


lemma cancel_ipc_cap_to:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. ex_nonz_cap_to p :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: cancel_ipc_caps_of_state
           simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state
       simp_del: split_paired_Ex)

lemma cancel_ipc_invs_st_tcb_at:
  "\<lbrace>invs\<rbrace> cancel_ipc t
   \<lbrace>\<lambda>rv. invs and st_tcb_at ((=) Running or (=) Inactive or (=) Restart or
                             (=) IdleThreadState) t
              and fault_tcb_at ((=) None) t:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: cancel_ipc_simple_except_awaiting_reply)

(* FIXME: move *)
lemma valid_sched_valid_blocked:
  "valid_sched s \<Longrightarrow> valid_blocked s" by (clarsimp simp: valid_sched_def)

(* FIXME: move *)
lemma valid_sched_valid_ready_qs:
  "valid_sched s \<Longrightarrow> valid_ready_qs s" by (clarsimp simp: valid_sched_def)

(* FIXME: move *)
lemma valid_sched_valid_release_q:
  "valid_sched s \<Longrightarrow> valid_release_q s" by (clarsimp simp: valid_sched_def)

lemma send_signal_BOR_helper:
  notes not_not_in_eq_in[iff] shows
  "ntfn_obj ntfn = IdleNtfn
   \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr
   \<Longrightarrow> \<lbrace>st_tcb_at ((=) (BlockedOnReceive ep r_opt)) tcbptr and ko_at (Notification ntfn) ntfnptr and
        valid_sched and invs and valid_ep_q and valid_machine_time and (\<lambda>s. tcbptr \<noteq> idle_thread s)\<rbrace>
         do y <- cancel_ipc tcbptr;
            y <- set_thread_state tcbptr Running;
            y <- as_user tcbptr (setRegister badge_register badge);
            y <- maybe_donate_sc tcbptr ntfnptr;
            in_release_q <- gets (in_release_queue tcbptr);
            schedulable <- is_schedulable tcbptr in_release_q;
            when schedulable (possible_switch_to tcbptr)
         od
       \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_sched_strong)
        apply (wpsimp wp: is_schedulable_wp)+
      apply (rule_tac Q="\<lambda>r s. tcbptr \<noteq> idle_thread s \<and> st_tcb_at runnable tcbptr s \<and>
                               valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s \<and>
      (active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> has_budget tcbptr s)" in hoare_strengthen_post[rotated])
       apply (clarsimp simp: obj_at_def valid_sched_def
                      split: option.splits dest!: get_tcb_SomeD)
       apply (clarsimp dest!: schedulable_unfold2 st_tcb_at_tcb_at)
       apply (intro conjI; intro allI impI)
        apply (intro conjI; intro allI impI)
         apply (clarsimp simp: not_in_release_q_def has_budget_def active_sc_tcb_at_defs)
        apply (erule valid_blocked_divided2)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                              runnable_eq_active)
       apply (erule valid_blocked_divided2)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                             active_sc_tcb_at_defs)
      apply (wpsimp wp: maybe_donate_sc_valid_ready_qs
                        maybe_donate_sc_valid_release_q
                        maybe_donate_sc_valid_sched_action
                        maybe_donate_sc_ct_not_in_q2
                        maybe_donate_sc_ct_in_cur_domain
                        maybe_donate_sc_valid_blocked_except_set maybe_donate_sc_cond_has_budget)
     apply wpsimp
    apply (rule_tac Q="\<lambda>xc s. (valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s)
                       \<and> not_queued tcbptr s \<and> scheduler_act_not tcbptr s \<and> not_in_release_q tcbptr s
                       \<and> tcbptr \<noteq> idle_thread s
                       \<and> st_tcb_at runnable tcbptr s \<and> valid_machine_time s \<and> has_budget tcbptr s \<and> invs s"
                    in hoare_strengthen_post[rotated])
     apply (clarsimp, frule invs_valid_objs, drule invs_sym_refs, simp)
    apply (rule hoare_vcg_conj_lift)
     apply (rule set_thread_state_break_valid_sched[simplified pred_conj_def])
    apply (wpsimp wp: sts_st_tcb_at' sts_cancel_ipc_Running_invs)
   apply (wpsimp wp: cancel_ipc_BOR_valid_sched cancel_ipc_BOR_other
      cancel_ipc_invs_st_tcb_at cancel_ipc_cap_to)
   apply (rule_tac Q="\<lambda>_. \<lambda>s. ((invs and st_tcb_at ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState)
              tcbptr and fault_tcb_at ((=) None) tcbptr) s \<and> ex_nonz_cap_to tcbptr s) \<and>
             (tcbptr \<noteq> idle_thread s)" in hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift[OF hoare_vcg_conj_lift[OF cancel_ipc_invs_st_tcb_at cancel_ipc_cap_to]
        cancel_ipc_it[where P="\<lambda>it. tcbptr \<noteq> it" ]])
   apply (wpsimp wp: hoare_vcg_conj_lift[OF cancel_ipc_invs_st_tcb_at cancel_ipc_cap_to]
             wp_del: cancel_ipc_invs)
  apply (clarsimp simp:)
  by (auto dest: valid_sched_valid_blocked elim!: pred_tcb_weakenE
           simp: live_def pred_tcb_at_eq_commute st_tcb_at_def obj_at_def
          intro!: valid_sched_not_runnable_scheduler_act_not
                  valid_sched_not_runnable_not_in_release_q
                  valid_eq_q_Blocked_on_Receive_has_budget
                  valid_sched_not_runnable_not_queued
                  if_live_then_nonz_cap_invs)

(* what can we say about ntfn_bound_tcb? can we say it is not equal to idle_thread or cur_thread? *)
lemma send_signal_valid_sched:
  "\<lbrace> valid_sched and invs and
      valid_ntfn_q and valid_ep_q and valid_machine_time\<rbrace>
     send_signal ntfnptr badge
   \<lbrace> \<lambda>_. valid_sched:: det_state \<Rightarrow> _ \<rbrace>"
  unfolding send_signal_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (case_tac "ntfn_bound_tcb ntfn"; clarsimp)
     apply wpsimp
    apply (rule hoare_seq_ext[OF _ gts_sp])
    apply (case_tac st; clarsimp simp: receive_blocked_def)
           prefer 4
           apply (rename_tac ep r_opt)
           apply (rule hoare_weaken_pre)
           apply (rule_tac ep = ep and r_opt = r_opt in send_signal_BOR_helper; simp)
           apply (clarsimp simp: pred_conj_def pred_tcb_at_def pred_tcb_at_eq_commute obj_at_def
                          split: option.splits)
           apply (drule invs_valid_idle, clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
          prefer 8
           apply (rename_tac queue)
          apply (wpsimp wp: send_signal_WaitingNtfn_helper)
          apply (subgoal_tac "queue \<noteq> [] \<and> tcb_at (hd queue) s")
             apply (subgoal_tac "(ntfnptr, TCBSignal) \<in> state_refs_of s (hd queue)")
              apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_refs_of_rev(5)[symmetric] obj_at_def
                                    state_refs_of_def)
             apply (rule sym_refsE)
              apply (rule invs_sym_refs, simp)
             apply (clarsimp simp: state_refs_of_def obj_at_def)
          apply (subgoal_tac "valid_ntfn ntfn s")
           apply (clarsimp simp: valid_ntfn_def)
          apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_objs_def valid_obj_def
                                dom_def obj_at_def)
         apply (wpsimp+)[8]
  done

lemma receive_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and ct_active
                and not_queued thread and scheduler_act_not thread and invs\<rbrace>
     receive_ipc thread cap is_blocking reply_cap
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
(*
  apply (simp add: receive_ipc_def)
  including no_pre
  apply (wp | wpc | simp add: get_sk_obj_ref_def update_sk_obj_ref_def)+
       apply (wp set_thread_state_sched_act_not_valid_sched | wpc)+
                 apply ((wp set_thread_state_sched_act_not_valid_sched
                        | simp add: do_nbrecv_failed_transfer_def)+)[2]
              apply ((wp possible_switch_to_valid_sched_weak sts_st_tcb_at' hoare_drop_imps
                          set_thread_state_runnable_valid_ready_qs
                          set_thread_state_runnable_valid_sched_action
                          set_thread_state_valid_blocked_except | simp | wpc)+)[3]
             apply simp
             apply (rule_tac Q="\<lambda>_. valid_sched and scheduler_act_not (sender) and not_queued (sender) and not_cur_thread (sender) and (\<lambda>s. sender \<noteq> idle_thread s)" in hoare_strengthen_post)
              apply wp
             apply (simp add: valid_sched_def)
            apply ((wp | wpc)+)[1]
           apply (simp | wp gts_wp hoare_vcg_all_lift)+
          apply (wp hoare_vcg_imp_lift)
           apply ((simp add: set_simple_ko_def set_object_def |
                   wp hoare_drop_imps | wpc)+)[1]
          apply (wp hoare_vcg_imp_lift get_object_wp
                    set_thread_state_sched_act_not_valid_sched gbn_wp
               | simp add: get_simple_ko_def do_nbrecv_failed_transfer_def a_type_def
                    split: kernel_object.splits
               | wpc
               | wp_once hoare_vcg_all_lift hoare_vcg_ex_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])+
  apply (clarsimp simp: st_tcb_at_kh_if_split default_notification_def default_ntfn_def isActive_def)
  apply (rename_tac xh xi xj)
  apply (drule_tac t="hd xh" and P'="\<lambda>ts. \<not> active ts" in st_tcb_weakenE)
   apply clarsimp
  apply (simp only: st_tcb_at_not)
  apply (subgoal_tac "hd xh \<noteq> idle_thread s")
   apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def valid_ready_qs_def st_tcb_at_not ct_in_state_def not_cur_thread_def runnable_eq_active not_queued_def scheduler_act_not_def split: scheduler_action.splits)
(* clag from send_signal_valid_sched *)
  apply clarsimp
  apply (frule invs_valid_idle)
  apply (drule_tac ptr=xc in idle_not_queued)
    apply (clarsimp simp: invs_sym_refs)
   apply (simp add: state_refs_of_def obj_at_def)
  apply (frule invs_valid_objs)
  apply (simp add: valid_objs_def obj_at_def)
  apply (drule_tac x = xc in bspec)
   apply (simp add: dom_def)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (drule hd_in_set)
  apply simp
  done*)
sorry (* receive_ipc_valid_sched *)

end

crunches schedule_tcb
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain'[wp]: "\<lambda>s. P (cur_domain s)"
  and valid_sched[wp]: valid_sched
  (simp: wp: hoare_drop_imp hoare_vcg_if_lift2 reschedule_valid_sched_const)

crunches maybe_return_sc
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: wp: hoare_drop_imp hoare_vcg_if_lift2 ignore: set_tcb_obj_ref)

lemma maybe_return_sc_valid_sched[wp]:
  "\<lbrace> valid_sched and scheduler_act_not tptr and not_queued tptr and not_in_release_q tptr\<rbrace>
       maybe_return_sc ntfnptr tptr \<lbrace> \<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: maybe_return_sc_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: pred_tcb_at_def obj_at_def valid_sched_def)
  apply (intro conjI)
    apply (clarsimp simp: valid_ready_qs_def not_queued_def st_tcb_at_kh_def
      etcb_defs refill_prop_defs active_sc_tcb_at_defs split: option.splits)
    apply (drule_tac x=d and y=p in spec2, clarsimp, intro conjI; clarsimp)
    apply (drule_tac x=t in bspec, simp, clarsimp simp: active_sc_tcb_at_defs split: option.splits)
     apply (intro conjI impI allI; fastforce)
    apply (solve_valid_release_q csimp: not_in_release_q_def st_tcb_at_kh_def)
   apply (clarsimp simp: valid_sched_action_def)
   apply (rule conjI)
    apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs refill_prop_defs
                  split: option.splits)
  by (fastforce simp: scheduler_act_not_def valid_blocked_def st_tcb_at_kh_def active_sc_tcb_at_defs
                  split: option.splits)+

crunches do_nbrecv_failed_transfer
for valid_sched[wp]: valid_sched
  (wp: valid_sched_lift)

lemma as_user_test_sc_refill_max[wp]:
  "\<lbrace>test_sc_refill_max scp\<rbrace> as_user tptr f \<lbrace>\<lambda>_. test_sc_refill_max scp\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def wp: get_object_def)
  by (clarsimp simp: test_sc_refill_max_def dest!: get_tcb_SomeD split: option.splits)

lemma maybe_donate_sc_bound_sc_trivial:
  "\<lbrace>bound_sc_tcb_at bound thread and P\<rbrace>
   maybe_donate_sc thread ntfn_ptr
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (wpsimp)
  apply (rule hoare_pre_cont)
  apply (wpsimp simp: get_sc_obj_ref_def get_sk_obj_ref_def get_tcb_obj_ref_def
                  wp: thread_get_wp get_simple_ko_wp)+
  apply (fastforce simp: obj_at_def pred_tcb_at_def)
  done

lemma receive_signal_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not thread and not_queued thread and not_in_release_q thread
                and (\<lambda>s. thread = cur_thread s) and bound_sc_tcb_at bound thread\<rbrace>
     receive_signal thread cap is_blocking \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: receive_signal_def)
  apply (cases cap; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
  apply (wpsimp wp: maybe_donate_sc_bound_sc_trivial)
  done

(*
crunch valid_sched: schedule_tcb,maybe_return_sc,maybe_donate_sc valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv)

crunch valid_sched: receive_signal valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv mapM_wp)
*)

crunches restart_thread_if_no_fault
  for not_queued[wp]: "not_queued t"
  (wp: crunch_wps)

context DetSchedSchedule_AI begin
lemma cancel_all_ipc_not_queued:
  "\<lbrace>st_tcb_at active t and valid_objs and not_queued t and scheduler_act_not t
        and sym_refs \<circ> state_refs_of\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (wp reschedule_required_not_queued  | wpc | simp)+
      apply (rule hoare_gen_asm)
      apply (rule_tac S="set queue - {t}" in mapM_x_wp)
       apply (wp tcb_sched_enqueue_not_queued gts_wp| clarsimp | wpc)+
      apply (erule notE, assumption)
     apply (wp reschedule_required_not_queued | simp add: get_ep_queue_def)+
     apply (rule hoare_gen_asm)
     apply (rule_tac S="set queue - {t}" in mapM_x_wp)
      apply (wp tcb_sched_enqueue_not_queued gts_wp | wpc | clarsimp)+
     apply (erule notE, assumption)
    apply (wp hoare_vcg_imp_lift
         | simp add: get_ep_queue_def get_simple_ko_def a_type_def get_object_def
              split: kernel_object.splits
         | wpc | wp_once hoare_vcg_all_lift)+
   apply safe
   apply (rename_tac xa)
   apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep="SendEP xa" in
          ep_queued_st_tcb_at[rotated, rotated])
       apply (simp_all only: st_tcb_at_not)
      apply (simp add: obj_at_def)+
  apply (rename_tac xa)
  apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep="RecvEP xa" in ep_queued_st_tcb_at[rotated, rotated])
      apply (simp_all only: st_tcb_at_not)
     apply (fastforce simp: obj_at_def)+
  done
end

lemma cancel_all_signals_not_queued:
  "\<lbrace>st_tcb_at active t and valid_objs and not_queued t and scheduler_act_not t
         and sym_refs \<circ> state_refs_of\<rbrace>
    cancel_all_signals epptr
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (wp reschedule_required_not_queued | wpc | simp)+
      apply (rename_tac list)
      apply (rule_tac P="(t \<notin> set list)" in hoare_gen_asm)
      apply (rule_tac S="set list - {t}" in mapM_x_wp)
       apply (wp tcb_sched_enqueue_not_queued | clarsimp)+
       apply blast+
     apply (wp hoare_vcg_imp_lift
      | simp add: get_simple_ko_def get_object_def a_type_def split: kernel_object.splits
      | wpc | wp_once hoare_vcg_all_lift)+
  apply safe
  apply (rename_tac ep x y)
  apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep=ep in
      ntfn_queued_st_tcb_at[rotated, rotated])
      apply (simp_all only: st_tcb_at_not)
     apply (fastforce simp: obj_at_def)+
  done

lemma unbind_maybe_notification_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
     unbind_maybe_notification a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_maybe_notification_def get_sk_obj_ref_def maybeM_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def, frule (4) ntfn_bound_tcb_at)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm, frule ko_at_state_refs_ofD, simp)+
   apply (frule_tac P="(=) (Some a)" in ntfn_bound_tcb_at, simp_all add: obj_at_def)[1]
  apply (clarsimp simp: obj_at_def, frule (4) ntfn_bound_tcb_at, clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (frule (1) sym_refs_ko_atD[simplified obj_at_def, simplified])
  apply (frule ko_at_state_refs_ofD[where ko="TCB _", simplified obj_at_def, simplified])
  apply (fastforce split: if_split_asm split del: if_split simp: get_refs_def2 obj_at_def)
  done


lemma sched_context_unbind_ntfn_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace>
   sched_context_unbind_ntfn sc_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_ntfn_def maybeM_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_ntfn sc"; clarsimp)
   apply wpsimp
  apply (wpsimp simp: update_sk_obj_ref_def
        wp: get_simple_ko_wp get_sched_context_wp)
  by (clarsimp simp: valid_obj_def valid_ntfn_def valid_bound_obj_def
               split: option.splits ntfn.splits elim!: obj_at_valid_objsE)

lemma sched_context_maybe_unbind_ntfn_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> sched_context_maybe_unbind_ntfn ntfn_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (clarsimp simp: sched_context_maybe_unbind_ntfn_def maybeM_def)
  apply (wpsimp simp: sched_context_maybe_unbind_ntfn_def get_sk_obj_ref_def
                      set_sc_obj_ref_def update_sk_obj_ref_def
                  wp: get_simple_ko_wp)
  by (clarsimp simp: valid_ntfn_def valid_bound_obj_def valid_obj_def
              split: option.splits ntfn.splits
              elim!: obj_at_valid_objsE)

lemma sched_context_unbind_ntfn_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
     sched_context_unbind_ntfn sc_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_ntfn_def get_sc_obj_ref_def maybeM_def)
  apply (rule hoare_seq_ext [OF _ get_sched_context_sp])
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (rule conjI)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm)
   apply (frule ko_at_state_refs_ofD)
   apply (frule ko_at_state_refs_ofD[where ko="Notification _"], simp)
  apply (frule (1) sym_refs_ko_atD)
  apply (frule ko_at_state_refs_ofD[where ko="Notification _"])
  apply (fastforce split: if_split_asm split del: if_split simp: image_iff get_refs_def2 obj_at_def)+
  done

lemma sched_context_maybe_unbind_ntfn_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
     sched_context_maybe_unbind_ntfn a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
(* FIXME rt: duplicated proof from sched_context_maybe_unbind_ntfn_invs, should cleanup*)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def update_sk_obj_ref_def
                      sched_context_maybe_unbind_ntfn_def maybeM_def get_sk_obj_ref_def
                  wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp
                      get_sched_context_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI, clarsimp)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def valid_bound_obj_def obj_at_def
                  dest!: is_sc_objD)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (auto dest: refs_in_ntfn_q_refs refs_in_get_refs
               simp: state_refs_of_def valid_ntfn_def obj_at_def is_sc_obj_def
              split: if_split_asm option.split_asm ntfn.splits kernel_object.split_asm)[1]
  apply (clarsimp split: if_splits)
   apply (solves \<open>clarsimp simp: state_refs_of_def\<close>
            | fastforce simp: obj_at_def
                       dest!: refs_in_get_refs SCNtfn_in_state_refsD ntfn_sc_sym_refsD)+
  done

crunch not_queued[wp]: sched_context_unbind_yield_from "not_queued t"
  (wp: hoare_drop_imps maybeM_inv mapM_x_wp')

crunch not_queued[wp]: sched_context_unbind_reply "not_queued t"
  (wp: hoare_drop_imps maybeM_inv mapM_x_wp')

lemma sched_context_unbind_tcb_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_unbind_tcb scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def
      wp: tcb_dequeue_not_queued_gen reschedule_required_not_queued get_sched_context_wp)

lemma sched_context_unbind_all_tcbs_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_unbind_all_tcbs scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def wp: get_sched_context_wp)

context DetSchedSchedule_AI begin

lemma fast_finalise_not_queued:
  "\<lbrace>valid_objs and sym_refs \<circ> state_refs_of and st_tcb_at active t and scheduler_act_not t
    and not_queued t\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (cases cap; simp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_not_queued)
    apply (wpsimp wp: cancel_all_signals_not_queued unbind_maybe_notification_valid_objs)
   apply (wpsimp wp: gts_wp get_simple_ko_wp)
  apply wpsimp
  done

end

lemma set_simple_ko_ct_active:
  "\<lbrace>ct_active\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def | wp get_object_wp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
                  split: kernel_object.splits)
  done

lemma cap_insert_check_cap_ext_valid[wp]:"
  \<lbrace>valid_list\<rbrace>
   check_cap_at new_cap src_slot (check_cap_at t slot (cap_insert new_cap src_slot x))
  \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (wp get_cap_wp | simp)+
  done

lemma opt_update_thread_valid_sched[wp]:
  "(\<And>x a. tcb_state (fn a x) = tcb_state x) \<Longrightarrow>
   (\<And>x a. tcb_sched_context (fn a x) = tcb_sched_context x) \<Longrightarrow>
   (\<And>x a. etcb_of (fn a x) = etcb_of x) \<Longrightarrow>
    \<lbrace>valid_sched\<rbrace> option_update_thread t fn v \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: option_update_thread_def)
   apply (wp thread_set_not_state_valid_sched | wpc | simp)+
  done

lemma opt_update_thread_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace>
    option_update_thread t fn v
   \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: option_update_thread_def)
   apply (wp | wpc | simp)+
  done

crunches lookup_cap,lookup_reply
for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and st_tcb_at[wp]: "st_tcb_at P t"
and not_queued[wp]: "not_queued t"
and not_in_release_q[wp]: "not_in_release_q t"
and scheduler_act_not[wp]: "scheduler_act_not t"
and active_sc_tcb_at[wp]: "active_sc_tcb_at t"
and budget_ready[wp]: "budget_ready t"
and budget_sufficient[wp]: "budget_sufficient t"
and invs[wp]: invs
and ct_active[wp]: ct_active
and ct_idle[wp]: ct_idle
and ct_active_or_idle[wp]: "ct_active or ct_idle"
and simple_sched_action[wp]: simple_sched_action
and valid_ep_q[wp]: valid_ep_q

lemma test:
"invs s \<longrightarrow> (\<exists>y. get_tcb thread s = Some y) \<longrightarrow> s \<turnstile> tcb_ctable (the (get_tcb thread s))"
apply (simp add: invs_valid_tcb_ctable_strengthen)
done

context DetSchedSchedule_AI begin

lemma budget_sufficient_bound_sc:
  "budget_sufficient t s \<Longrightarrow> bound_sc_tcb_at bound t s"
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active and ct_not_in_release_q and valid_ep_q
      and ct_not_queued and scheduler_act_sane and ct_ARS\<rbrace>
   handle_recv is_blocking can_reply \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong split del: if_split)
  apply (wpsimp wp: get_simple_ko_wp handle_fault_valid_sched
                    receive_ipc_valid_sched receive_signal_valid_sched
              simp: whenE_def get_sk_obj_ref_def
         split_del: if_split)+
     apply (rule hoare_vcg_E_elim)
      apply (wpsimp simp: lookup_cap_def lookup_slot_for_thread_def)
       apply (wp resolve_address_bits_valid_fault2)+
     apply (simp add: valid_fault_def)
     apply (wp hoare_drop_imps hoare_vcg_all_lift_R)
    apply (wpsimp cong: conj_cong | strengthen invs_valid_tcb_ctable_strengthen)+
  apply (auto simp: ct_in_state_def tcb_at_invs objs_valid_tcb_ctable invs_valid_objs
              dest: budget_sufficient_bound_sc)
  done
(*
lemma handle_recv_valid_sched':
  "\<lbrace>invs and valid_sched and ct_active and ct_not_queued and scheduler_act_sane
 and ct_not_in_release_q and valid_ep_q and ct_ARS\<rbrace>
    handle_recv is_blocking can_reply
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: handle_recv_valid_sched)
  done
*)
crunch valid_sched[wp]: reply_from_kernel "valid_sched::det_state \<Rightarrow> _"

end

context DetSchedSchedule_AI begin
crunch valid_sched[wp]: invoke_irq_control "valid_sched::det_state \<Rightarrow> _"
  (wp: maybeM_inv)

lemma invoke_irq_handler_valid_sched[wp]:
  "\<lbrace> valid_sched and invs and simple_sched_action
     and valid_ep_q and valid_ntfn_q\<rbrace>
   invoke_irq_handler i
   \<lbrace> \<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (cases i; wpsimp wp: cap_delete_one_valid_sched)

end

declare valid_idle_etcb_lift[wp del]

crunches thread_set_domain
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  and sched[wp]: "\<lambda>s. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and in_release_queue'[wp]: "\<lambda>s. P (in_release_queue t s)"
  (simp: in_release_queue_def)

lemma thread_set_domain_st_tcb[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (st_tcb_at Q p s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

(*
lemma thread_set_domain_not_activatable_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb and valid_idle and st_tcb_at (\<lambda>ts. \<not> activatable ts) tptr\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_idle_etcb_def etcb_at'_def etcbs_of'_def valid_idle_def
                        pred_tcb_at_def obj_at_def)
  done
*)

(*
lemma thread_set_domain_not_activatable_valid_sched:
  "\<lbrace>valid_sched and valid_idle and st_tcb_at (\<lambda>ts. \<not> activatable ts) tptr\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_sched_action_def | wp ethread_set_not_queued_valid_ready_qs ethread_set_not_switch_switch_in_cur_domain ethread_set_not_cur_ct_in_cur_domain ethread_set_valid_blocked ethread_set_not_activatable_valid_idle_etcb)+
        apply (force simp: valid_idle_def st_tcb_at_def obj_at_def not_cur_thread_def
                           is_activatable_def weak_valid_sched_action_def valid_ready_qs_def
                           not_queued_def split: thread_state.splits)+
  done *)

lemma thread_set_domain_not_idle_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb and valid_idle and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_idle_etcb_def etcb_at'_def etcbs_of'_def valid_idle_def
                        pred_tcb_at_def obj_at_def)
  done

lemma thread_set_domain_cur_activatable[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>"
  unfolding is_activatable_def
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: hoare_vcg_imp_lift)

lemma thread_set_domain_active_sc_tcb_at[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P], rule iffI; force?)
  apply (clarsimp; rule_tac x=scp in exI, force)
  done

lemma thread_set_domain_budget_ready[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P], rule iffI; force?)
  apply (clarsimp; rule_tac x=scp in exI, force)
  done

lemma thread_set_domain_budget_sufficient[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P], rule iffI; force?)
  apply (clarsimp; rule_tac x=scp in exI, force)
  done

lemma thread_set_domain_weak_valid_sched_action[wp]:
  "thread_set_domain tptr d \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding weak_valid_sched_action_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma thread_set_domain_not_switch_switch_in_cur_domain:
  "\<lbrace>switch_in_cur_domain and (\<lambda>s. scheduler_action s \<noteq> switch_thread tptr)\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def is_etcb_at_def etcb_at_def etcbs_of'_def
                 dest!:get_tcb_SomeD)
  done

lemma thread_set_domain_ssa_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_not_switch_switch_in_cur_domain)
  apply (force simp: simple_sched_action_def)
  done

lemma thread_set_domain_act_not_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tptr\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_not_switch_switch_in_cur_domain)
  apply (force simp: scheduler_act_not_def)
  done

lemma thread_set_domain_valid_blocked_except:
  "\<lbrace>valid_blocked_except t\<rbrace> thread_set_domain tptr d \<lbrace>\<lambda>_. valid_blocked_except t\<rbrace>"
  by (wpsimp wp: valid_blocked_except_lift)

lemma thread_set_domain_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace> thread_set_domain tptr d \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  by (wpsimp wp: valid_blocked_lift)

lemma thread_set_domain_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain and not_cur_thread t\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_2_def etcb_at'_def etcbs_of'_def
                        not_cur_thread_def)
  done

lemma thread_set_domain_not_cur_thread[wp]:
  "thread_set_domain t d \<lbrace>not_cur_thread t\<rbrace>"
  unfolding not_cur_thread_def by (wpsimp wp: hoare_vcg_imp_lift)

lemma thread_set_domain_valid_ready_qs_not_q:
  "\<lbrace>valid_ready_qs and not_queued t\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ready_qs_def etcb_defs active_sc_tcb_at_defs refill_prop_defs not_queued_def
                  dest!: get_tcb_SomeD split: option.splits)
  apply (intro conjI; clarsimp)
  apply (drule_tac x=da and y =p in spec2, clarsimp, drule_tac x=ta in bspec, simp)
  by (fastforce simp: st_tcb_at_kh_def st_tcb_at_def active_sc_tcb_at_defs)

lemma thread_set_domain_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> thread_set_domain tptr d \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp wp: set_object_wp) solve_valid_release_q

lemma thread_set_domain_ct_not_in_q[wp]:
  "thread_set_domain p d \<lbrace>ct_not_in_q\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp wp: set_object_wp)

lemma thread_set_domain_not_idle_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not tptr and not_queued tptr
     and (\<lambda>s. tptr \<noteq> cur_thread s) and (\<lambda>s. tptr \<noteq> idle_thread s) and valid_idle\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_valid_ready_qs_not_q thread_set_domain_ct_in_cur_domain
                    thread_set_domain_not_switch_switch_in_cur_domain valid_blocked_lift
                    thread_set_domain_not_idle_valid_idle_etcb
                    thread_set_domain_valid_release_q)
  apply (clarsimp simp: scheduler_act_not_def not_cur_thread_def)
  done

declare tcb_sched_action_valid_idle_etcb[wp]

lemma thread_set_domain_schedulable_bool_not[wp]:
  "\<lbrace>\<lambda>s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        thread_set_domain t d
           \<lbrace>\<lambda>rv s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: thread_set_domain_def thread_set_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_rev is_schedulable_bool_def test_sc_refill_max_def in_release_queue_def
        dest!: get_tcb_SomeD split: option.splits if_split_asm)

lemma thread_set_domain_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        thread_set_domain t d
           \<lbrace>\<lambda>rv s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: thread_set_domain_def thread_set_def wp: set_object_wp)
  by (fastforce simp: get_tcb_rev is_schedulable_bool_def test_sc_refill_max_def in_release_queue_def
        dest!: get_tcb_SomeD split: option.splits)

lemma tcb_sched_action_schedulable_bool_not[wp]:
  "\<lbrace>\<lambda>s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        tcb_sched_action f t
           \<lbrace>\<lambda>rv s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_set_def thread_get_def wp: set_object_wp)
  by (clarsimp simp: is_schedulable_bool_def get_tcb_rev obj_at_def dest!: get_tcb_SomeD split: option.splits)

lemma tcb_sched_action_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        tcb_sched_action f t
   \<lbrace>\<lambda>rv s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_set_def thread_get_def wp: set_object_wp)
  by (fastforce simp: is_schedulable_bool_def get_tcb_rev obj_at_def dest!: get_tcb_SomeD split: option.splits)

(* move *)
lemma valid_sched_action_switch_thread_is_schedulable:
  "\<lbrakk>valid_sched_action s; scheduler_action s = switch_thread thread\<rbrakk> \<Longrightarrow>
     is_schedulable_opt thread (in_release_queue thread s) s = Some True"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
       is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def get_tcb_rev
       in_release_queue_def)

(* move *)
lemma reschedule_valid_sched:
  "\<lbrace>valid_ready_qs and valid_release_q and ct_not_in_q and
    valid_sched_action and valid_blocked and valid_idle_etcb\<rbrace>
     reschedule_required
   \<lbrace>\<lambda>rv. valid_sched \<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def tcb_sched_action_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action)
  apply (wpsimp wp: tcb_sched_enqueue_valid_sched reschedule_valid_sched_const)
    apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_blocked_def)
   apply (rename_tac thread)
   apply (clarsimp simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
   apply (rule_tac Q="K (xa = the (Some True)) and
         (valid_ready_qs and valid_release_q and ct_not_in_q and
          valid_sched_action and
          valid_blocked and
          valid_idle_etcb and (\<lambda>s. scheduler_action s = switch_thread thread)) and (\<lambda>s. in_release_queue thread s = x)" in hoare_weaken_pre)
    apply (wpsimp simp: thread_get_def)
    apply (clarsimp simp: valid_sched_def)
    apply (rule conjI)
     apply (clarsimp simp: valid_ready_qs_2_def valid_sched_action_2_def tcb_sched_enqueue_def
                           weak_valid_sched_action_2_def etcbs_of'_def is_etcb_at'_def
                           etcb_at_def obj_at_def pred_tcb_at_def
                           is_refill_sufficient_def is_refill_ready_def
                    dest!: ko_at_etcbD get_tcb_SomeD)
    apply (rule conjI)
     apply (clarsimp simp: ct_not_in_q_2_def)
    apply (clarsimp simp: valid_blocked_def not_queued_def tcb_sched_enqueue_def)
    apply fastforce
   apply (simp only: pred_conj_def, elim conjE)
   apply (frule (1) valid_sched_action_switch_thread_is_schedulable, clarsimp)
  apply wpsimp
  apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_blocked_def)
  done

crunches tcb_sched_action
for valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"

lemma thread_set_domain_is_schedulable_opt[wp]:
  "\<lbrace>\<lambda>s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>
   thread_set_domain t d
   \<lbrace>\<lambda>rv s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>"
  unfolding thread_set_domain_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: is_schedulable_opt_def get_tcb_def
test_sc_refill_max_def in_release_queue_def
 split: option.splits kernel_object.splits cong: conj_cong | safe)+
  done

lemma tcb_sched_dequeue_is_schedulable_opt[wp]:
  "\<lbrace>\<lambda>s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>
   tcb_sched_action tcb_sched_dequeue t
   \<lbrace>\<lambda>rv s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>"
  unfolding tcb_sched_action_def
  apply (wpsimp wp: thread_set_wp)
  done

lemma valid_blocked_valid_ready_qs_ready_and_sufficient:
  "\<lbrakk>t \<noteq> cur_thread s; valid_ready_qs s; valid_blocked s;
          scheduler_act_not t s;
          st_tcb_at runnable t s; active_sc_tcb_at t s; not_in_release_q t s\<rbrakk>
         \<Longrightarrow> budget_ready t s \<and> budget_sufficient t s"
  apply (clarsimp simp: valid_blocked_def pred_tcb_at_eq_commute)
  apply (case_tac "not_queued t s")
   apply (drule_tac x=t in spec)
   apply (clarsimp simp: scheduler_act_not_def pred_tcb_at_def obj_at_def)
   apply (case_tac "tcb_state tcb"; simp)
  apply (clarsimp simp: valid_ready_qs_def not_queued_def)
  done

lemma invoke_domain_valid_sched:
  notes tcb_sched_enqueue_valid_sched[wp del]
  shows
  "\<lbrace>valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and ct_not_queued
                and scheduler_act_not t and valid_idle and ready_or_released and
                    (\<lambda>s. budget_sufficient (cur_thread s) s \<and> budget_ready (cur_thread s) s)\<rbrace>
     invoke_domain t d
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (simp add: invoke_domain_def)
  including no_pre
  apply wp
  apply (simp add: set_domain_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac "t=cur"; simp)
    (* first case *)
   apply (wpsimp wp_del: reschedule_valid_sched_const wp: reschedule_required_valid_sched')
       apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const) (* careful here *)
      apply (wpsimp wp: is_schedulable_wp)+
    apply (rule_tac Q="\<lambda>_. valid_release_q and weak_valid_sched_action and valid_blocked
                           and valid_idle_etcb and valid_ready_qs and budget_sufficient t
                           and budget_ready t" in hoare_strengthen_post[rotated])
     apply (clarsimp split: if_splits dest!: is_schedulable_opt_Some)
    apply (wpsimp wp: valid_blocked_lift thread_set_domain_not_idle_valid_idle_etcb thread_set_domain_valid_ready_qs_not_q)
   apply (rule hoare_weaken_pre)
    apply (wpsimp wp: tcb_sched_dequeue_valid_blocked_except_set_remove tcb_sched_dequeue_valid_ready_qs
                      tcb_dequeue_not_queued_gen)
   apply (clarsimp simp: valid_sched_def valid_sched_action_def)
    (* second case *)
  apply (wpsimp wp: tcb_sched_enqueue_valid_sched)
     apply (wpsimp wp: is_schedulable_wp)+
   apply (rule_tac Q="\<lambda>_. valid_sched_except_blocked and (\<lambda>s. cur_thread s = cur) and
                          (\<lambda>s. is_schedulable_opt t (in_release_queue t s) s = Some True \<longrightarrow>
                               valid_blocked_except_set {t} s \<and>
                               budget_ready t s \<and> budget_sufficient t s) and (
                          (\<lambda>s. is_schedulable_opt t (in_release_queue t s) s = Some False \<longrightarrow>
                               valid_blocked s))"
  in hoare_strengthen_post[rotated])
    apply ((clarsimp simp: not_cur_thread_def valid_sched_def split: if_splits dest!: is_schedulable_opt_Some)+)[1]
   apply (wpsimp wp: valid_blocked_lift thread_set_domain_not_idle_valid_idle_etcb thread_set_domain_valid_ready_qs_not_q
                     thread_set_domain_act_not_valid_sched_action thread_set_domain_ct_in_cur_domain)
   apply (wpsimp wp: hoare_vcg_imp_lift' thread_set_domain_valid_blocked_except thread_set_domain_valid_blocked)
  apply (rule hoare_weaken_pre)
   apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued hoare_vcg_imp_lift'
                     tcb_sched_dequeue_valid_blocked_except_set
                     tcb_sched_dequeue_valid_blocked_except_set_const)
  by (clarsimp simp: valid_sched_def not_cur_thread_def;
      fastforce simp: not_in_release_q_def in_release_queue_def runnable_eq_active
               dest!: is_schedulable_opt_Some valid_blocked_valid_ready_qs_ready_and_sufficient)

lemma cap_insert_cur_sc_chargeable[wp]:
  "cap_insert a' b' c' \<lbrace>cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: cur_sc_chargeable_lift)

context DetSchedSchedule_AI begin

lemma sched_context_bind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     sched_context_bind_ntfn x21 x41
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
 unfolding sched_context_bind_ntfn_def
 by wpsimp

lemma tcb_yield_to_update_has_budget[wp]:
  "set_tcb_obj_ref tcb_yield_to_update ct_ptr (Some sc_ptr)
   \<lbrace>has_budget tcb_ptr:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: has_budget_equiv2 wp: hoare_vcg_disj_lift)

lemma sc_yield_from_update_has_budget[wp]:
  "set_sc_obj_ref sc_yield_from_update ct_ptr (Some sc_ptr)
   \<lbrace>has_budget tcb_ptr:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: has_budget_equiv2 wp: hoare_vcg_disj_lift)

lemma sc_yield_from_update_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_sc_obj_ref sc_yield_from_update sc_ptr ref \<lbrace>\<lambda>_. valid_ready_qs:: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_sc_obj_ref_def update_sched_context_def)
  apply (wp get_object_wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma sc_yield_from_update_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_sc_obj_ref sc_yield_from_update sc_ptr ref \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_sc_obj_ref_def update_sched_context_def)
  apply (wp get_object_wp | wpc | simp add: set_object_def)+
  apply (intro conjI impI allI; clarsimp simp: valid_release_q_def sc_refills_sc_at_def obj_at_def; rule conjI)
   apply (fastforce simp: active_sc_tcb_at_defs st_tcb_at_kh_def not_in_release_q_def
                   split: if_splits)
  apply (clarsimp simp: sorted_release_q_def active_sc_tcb_at_defs elim!: sorted_wrt_mono_rel[rotated])
  by (((rename_tac x y; frule_tac x=x in bspec, simp, drule_tac x=y in bspec, simp)+);
       fastforce simp: tcb_ready_time_kh_def tcb_ready_time_def get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

lemma set_sc_obj_ref_ct_in_cur_domain[wp]:
  "set_sc_obj_ref f ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding set_sc_obj_ref_def update_sched_context_def
  apply (wpsimp simp: set_object_def get_object_def)
  by (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcbs_of'_def etcb_at'_def
              dest!: get_tcb_SomeD)

lemma set_sc_yield_from_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_sc_obj_ref sc_yield_from_update tptr ref \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: sc_yield_from_update_valid_sched_parts)

(*
lemma refill_unblock_check_valid_sched:
  "\<lbrace>valid_sched and sc_not_in_release_q a and valid_machine_time\<rbrace>
    refill_unblock_check a \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: refill_unblock_check_valid_ready_qs refill_unblock_check_valid_release_q
                 refill_unblock_check_valid_sched_action refill_unblock_check_ct_in_cur_domain)

lemma refill_unblock_check_valid_sched':
  "\<lbrace>valid_sched and sc_not_in_release_q scp and valid_machine_time\<rbrace>
    refill_unblock_check scp
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: refill_unblock_check_valid_ready_qs refill_unblock_check_valid_release_q'
                 refill_unblock_check_valid_sched_action refill_unblock_check_ct_in_cur_domain)

*)
lemma active_sc_tcb_at_cur_thread_lift:
  assumes A: "\<And>t. f \<lbrace>\<lambda>s. t \<noteq> (cur_thread s)\<rbrace>"
  assumes B: "\<And>t. f \<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>r s. \<forall>t. t = (cur_thread s) \<longrightarrow> active_sc_tcb_at t s" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' A B)
  apply (clarsimp simp: active_sc_tcb_at_def)
  done

lemma budget_ready_cur_thread_lift_pre_conj:
  assumes A: "\<And>t. \<lbrace>\<lambda>s. t \<noteq> (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. t \<noteq> (cur_thread s)\<rbrace>"
  assumes B: "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. budget_ready t s\<rbrace>"
  shows "\<lbrace>\<lambda>s. budget_ready (cur_thread s) s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. budget_ready (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>r s. \<forall>t. t = (cur_thread s) \<longrightarrow> budget_ready t s" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' A B)
  apply (clarsimp simp: bound_sc_tcb_at_def)
  done

lemmas budget_ready_cur_thread_lift = budget_ready_cur_thread_lift_pre_conj[where R=\<top>, simplified]

lemma budget_sufficient_cur_thread_lift:
  assumes A: "\<And>t. f \<lbrace>\<lambda>s. t \<noteq> (cur_thread s)\<rbrace>"
  assumes B: "\<And>t. f \<lbrace>\<lambda>s. budget_sufficient t s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>r s. \<forall>t. t = (cur_thread s) \<longrightarrow> budget_sufficient t s" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' A B)
  apply (clarsimp simp: bound_sc_tcb_at_def)
  done

lemma ct_ARS_lift:
  assumes A: "\<And>t. f \<lbrace>\<lambda>s. t \<noteq> (cur_thread s)\<rbrace>"
  assumes B: "\<And>t. f \<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>"
  assumes C: "\<And>t. f \<lbrace>\<lambda>s. budget_ready t s\<rbrace>"
  assumes D: "\<And>t. f \<lbrace>\<lambda>s. budget_sufficient t s\<rbrace>"
  shows "f \<lbrace>ct_ARS\<rbrace>"
  by (wpsimp wp: A B C D active_sc_tcb_at_cur_thread_lift budget_ready_cur_thread_lift
                    budget_sufficient_cur_thread_lift)

lemma complete_yield_to_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
   complete_yield_to y
   \<lbrace>\<lambda>rv. active_sc_tcb_at t ::det_state \<Rightarrow> _\<rbrace>"
  unfolding complete_yield_to_def
  by (wpsimp wp: hoare_drop_imps)

lemma complete_yield_to_budget_ready[wp]:
  "\<lbrace>budget_ready t\<rbrace>
   complete_yield_to y
   \<lbrace>\<lambda>rv. budget_ready t ::det_state \<Rightarrow> _\<rbrace>"
  unfolding complete_yield_to_def
  by (wpsimp wp: hoare_drop_imps)

lemma complete_yield_to_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient t\<rbrace>
   complete_yield_to y
   \<lbrace>\<lambda>rv. budget_sufficient t ::det_state \<Rightarrow> _\<rbrace>"
  unfolding complete_yield_to_def
  by (wpsimp wp: hoare_drop_imps)

crunches complete_yield_to, sched_context_resume
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma refill_unblock_check_budget_ready_ct[wp]:
  "\<lbrace>\<lambda>s. budget_ready (cur_thread s) s \<and> valid_machine_time s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_ready (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf_pre_conj[where f=cur_thread]) wpsimp+

lemma refill_unblock_check_budget_sufficient_ct[wp]:
  "\<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_sufficient (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma refill_unblock_check_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma sched_context_update_consumed_sc_tcb_sc_at[wp]:
  "sched_context_update_consumed e \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  unfolding sched_context_update_consumed_def
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  by (clarsimp simp: obj_at_def sc_tcb_sc_at_def)

lemma set_consumed_sc_tcb_sc_at[wp]:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at P scp s\<rbrace>
   set_consumed sp buf
   \<lbrace> \<lambda>rv s. sc_tcb_sc_at P scp s\<rbrace>"
  apply (simp add: set_consumed_def)
  by (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
 simp: split_def set_message_info_def as_user_def set_mrs_def set_object_def sc_tcb_sc_at_def zipWithM_x_mapM)

lemma budget_ready_tcb_non_sc_update_kheap:
  "\<lbrakk>kheap s t = Some (TCB tcb); budget_ready t' s; tcb_sched_context tcb = tcb_sched_context tcb'\<rbrakk>
     \<Longrightarrow> budget_ready t' (s\<lparr>kheap := kheap s(t \<mapsto>TCB (tcb'))\<rparr>)"
  by (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
     (intro conjI; clarsimp; rule_tac x=scp in exI, clarsimp)+

lemma budget_sufficient_tcb_non_sc_update_kheap:
  "\<lbrakk>kheap s t = Some (TCB tcb); budget_sufficient t' s; tcb_sched_context tcb = tcb_sched_context tcb'\<rbrakk>
     \<Longrightarrow> budget_sufficient t' (s\<lparr>kheap := kheap s(t \<mapsto>TCB (tcb'))\<rparr>)"
  by (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)
     (intro conjI; clarsimp; rule_tac x=scp in exI, clarsimp)+

lemma budget_ready_sc_non_refill_update_kheap:
  "\<lbrakk>kheap s scp = Some (SchedContext sc n); budget_ready t s; sc_refills sc = sc_refills sc'\<rbrakk>
     \<Longrightarrow> budget_ready t (s\<lparr>kheap := kheap s(scp \<mapsto> SchedContext (sc') n)\<rparr>)"
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_ready_def)

lemma budget_sufficient_sc_non_refill_update_kheap:
  "\<lbrakk>kheap s scp = Some (SchedContext sc n); budget_sufficient t s; sc_refills sc = sc_refills sc'\<rbrakk>
     \<Longrightarrow> budget_sufficient t (s\<lparr>kheap := kheap s(scp \<mapsto> SchedContext (sc') n)\<rparr>)"
  by (fastforce simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def)

lemma ssyf_sc_tcb_sc_at_inv:
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  set_sc_obj_ref sc_yield_from_update sp new
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (simp add: set_sc_obj_ref_def update_sched_context_def)
  apply (wp get_object_wp | simp add: set_object_def sc_tcb_sc_at_def | wpc)+
  by (clarsimp simp: obj_at_def fun_upd_def[symmetric] budget_ready_sc_non_refill_update_kheap
                      budget_sufficient_sc_non_refill_update_kheap)

lemma styt_sc_tcb_sc_at_inv:
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  set_tcb_obj_ref tcb_yield_to_update  sp new
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp get_object_wp | simp add: set_object_def sc_tcb_sc_at_def | wpc)+
  by (clarsimp simp: obj_at_def get_tcb_def
                     budget_ready_tcb_non_sc_update_kheap budget_sufficient_tcb_non_sc_update_kheap
              split: option.splits kernel_object.splits | subst fun_upd_apply[symmetric])+

crunch sc_tcb_sc_at_inv[wp]: do_machine_op "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                \<and> budget_ready t s \<and> budget_sufficient t s) scp s"
  (simp: crunch_simps split_def sc_tcb_sc_at_def wp: crunch_wps hoare_drop_imps)

crunch sc_tcb_sc_at_inv[wp]: store_word_offs "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                \<and> budget_ready t s \<and> budget_sufficient t s) scp s"
  (simp: crunch_simps split_def wp: crunch_wps hoare_drop_imps ignore: do_machine_op)

lemma set_mrs_sc_tcb_sc_at_inv':
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  set_mrs thread buf msgs
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp split_del: if_split
              simp: split_def set_object_def zipWithM_x_mapM)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def get_tcb_def fun_upd_def[symmetric]
                     budget_ready_tcb_non_sc_update_kheap budget_sufficient_tcb_non_sc_update_kheap
              split: option.splits kernel_object.splits)

lemma set_message_info_sc_tcb_sc_at_inv:
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  set_message_info thread info
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (simp add: set_message_info_def)
  apply (wpsimp wp: get_object_wp hoare_drop_imp split_del: if_split
              simp: split_def as_user_def set_object_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def get_tcb_def fun_upd_def[symmetric]
                     budget_ready_tcb_non_sc_update_kheap budget_sufficient_tcb_non_sc_update_kheap
              split: option.splits kernel_object.splits)

lemma sched_context_update_consumed_sc_tcb_sc_at_inv':
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  sched_context_update_consumed sp
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp wp: get_object_wp get_sched_context_wp hoare_drop_imp split_del: if_split
           simp: split_def update_sched_context_def set_object_def)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def get_tcb_def fun_upd_def[symmetric]
                     budget_ready_sc_non_refill_update_kheap
                     budget_sufficient_sc_non_refill_update_kheap
              split: option.splits kernel_object.splits)

lemma set_consumed_sc_tcb_sc_at_inv':
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
  set_consumed sp buf
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (clarsimp simp: set_consumed_def)
  by (wpsimp wp: get_object_wp mapM_wp' hoare_drop_imp set_mrs_sc_tcb_sc_at_inv'
                 sched_context_update_consumed_sc_tcb_sc_at_inv' set_message_info_sc_tcb_sc_at_inv
      split_del: if_split
           simp: split_def as_user_def set_object_def sc_tcb_sc_at_def zipWithM_x_mapM)

lemma complete_yield_to_sc_tcb_sc_at':
  "\<lbrace>(\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                \<and> budget_ready t s \<and> budget_sufficient t s) scp s) \<rbrace>
   complete_yield_to tcb_ptr
  \<lbrace>\<lambda>rv s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                                 \<and> budget_ready t s \<and> budget_sufficient t s) scp s \<rbrace>"
  apply (clarsimp simp: complete_yield_to_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ gyt_sp])
  apply (case_tac yt_opt; clarsimp split del: if_split)
   apply wpsimp
  by (wpsimp wp: set_consumed_sc_tcb_sc_at_inv' ssyf_sc_tcb_sc_at_inv
                 hoare_vcg_ex_lift lookup_ipc_buffer_inv hoare_drop_imp
    | wps)+

lemma complete_yield_to_ct_ARS[wp]:
  "\<lbrace>ct_ARS\<rbrace> complete_yield_to tptr \<lbrace>\<lambda>_. ct_ARS :: det_state \<Rightarrow> _\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp+)

(* from previous version *)
(* FIXME: check if used *)
crunches complete_yield_to
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

crunches complete_yield_to
  for release_queue: "\<lambda>s::det_state. P (release_queue s)"
  (wp: crunch_wps simp: crunch_simps)

(* end *)

lemma sched_context_yield_to_valid_sched_helper:
  "\<lbrace>sc_yf_sc_at ((=) sc_yf_opt) sc_ptr and
       (valid_sched and simple_sched_action and
        (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s) and
        ct_active and ct_ARS and valid_machine_time and invs)\<rbrace>
     when (sc_yf_opt \<noteq> None) $
       do complete_yield_to (the sc_yf_opt);
          sc_yf_opt <- get_sc_obj_ref sc_yield_from sc_ptr;
          assert (sc_yf_opt = None)
       od
   \<lbrace>\<lambda>_. valid_sched and simple_sched_action and
     (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s) and
     ct_active and ct_ARS and invs and valid_machine_time\<rbrace>"
  by (wpsimp wp: complete_yield_to_sc_tcb_sc_at' get_sc_obj_ref_wp complete_yield_to_invs
                 hoare_vcg_all_lift hoare_drop_imp is_schedulable_wp)

lemma sched_context_resume_ready_and_sufficient:
  "\<lbrace> invs and valid_sched and bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr\<rbrace>
    sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>rv s::det_state. is_schedulable_bool tcbptr (in_release_q tcbptr s) s
                \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_resume_def maybeM_def assert_opt_def refill_ready_def refill_sufficient_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (clarsimp simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (clarsimp simp: get_refills_def)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (case_tac "runnable ts \<and> 0 < sc_refill_max sc \<and>
                     (r_time (refill_hd sca) \<le> xa + kernelWCET_ticks \<longrightarrow>
                          \<not> sufficient_refills 0 (sc_refills scb))"; clarsimp)
      (* \<not> (ready \<and> sufficient) *)
    apply (rule_tac Q="\<lambda>_. in_release_q tcbptr" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: is_schedulable_bool_def split: option.splits)
    apply (wpsimp wp: postpone_in_release_q)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def pred_tcb_at_def)
    apply (drule invs_sym_refs)
    apply (drule (1) ARM.sym_ref_tcb_sc[where tp=tcbptr])
     apply (drule sym[where s="Some sc_ptr"], simp)
    apply clarsimp
   apply wpsimp
   apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs is_schedulable_bool_def
                  split: option.splits dest!: get_tcb_SomeD)
  apply wpsimp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule invs_sym_refs)
  apply (drule (1) ARM.sym_ref_tcb_sc[where tp=tcbptr])
   apply (drule sym[where s="Some sc_ptr"], simp)
  apply clarsimp
  apply (clarsimp simp: in_release_q_def in_release_queue_def)
  done

lemma sched_context_resume_schedulable:
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr and
       (\<lambda>s. is_schedulable_bool tcbptr (in_release_q tcbptr s) s) and
        budget_ready tcbptr and budget_sufficient tcbptr\<rbrace>
    sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>rv s. is_schedulable_bool tcbptr (in_release_q tcbptr s) s\<rbrace>"
  unfolding sched_context_resume_def maybeM_def assert_opt_def refill_ready_def refill_sufficient_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (clarsimp simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (clarsimp simp: get_refills_def)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (case_tac "runnable ts \<and>
                      0 < sc_refill_max sc \<and>
                      (r_time (refill_hd sca) \<le> xa + kernelWCET_ticks \<longrightarrow>
                          \<not> sufficient_refills 0 (sc_refills scb))"; clarsimp)
      (* \<not> (ready \<and> sufficient) *)
    apply (wp hoare_pre_cont)
    apply (clarsimp simp: active_sc_tcb_at_defs refill_prop_defs)
  by wpsimp+

crunches sched_context_resume
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P p s)"
    (wp: crunch_wps simp: crunch_simps)

lemma schedulable_not_in_release_q:
  "is_schedulable_bool tp (in_release_q tp s) s \<Longrightarrow> not_in_release_q tp s"
  by (clarsimp simp: is_schedulable_bool_def not_in_release_q_def
               split: option.splits)


lemma sched_context_yield_to_valid_sched_helper2:
  "\<lbrace>sc_tcb_sc_at ((=) (Some tcb_ptr)) sc_ptr and
          (valid_sched and simple_sched_action and
           (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s)
                  sc_ptr s) and
           ct_active and
           ct_ARS and
           invs and valid_machine_time) and
           (\<lambda>s. is_schedulable_bool tcb_ptr (in_release_q tcb_ptr s) s
                \<longrightarrow> budget_ready tcb_ptr s \<and> budget_sufficient tcb_ptr s) \<rbrace>
   do in_release_q <- gets (in_release_queue tcb_ptr);
      schedulable <- is_schedulable tcb_ptr in_release_q;
      if schedulable
      then do y <- refill_unblock_check sc_ptr;
              sc <- get_sched_context sc_ptr;
              cur_time <- gets cur_time;
              y <-
              assert
               (sufficient_refills 0 (sc_refills sc) \<and>
                r_time (refill_hd sc) \<le> cur_time + kernelWCET_ticks);
              ct_ptr <- gets cur_thread;
              prios <- thread_get tcb_priority tcb_ptr;
              ct_prios <- thread_get tcb_priority ct_ptr;
              if prios < ct_prios
              then do y <- tcb_sched_action tcb_sched_dequeue tcb_ptr;
                      y <- tcb_sched_action tcb_sched_enqueue tcb_ptr;
                      set_consumed sc_ptr args
                   od
              else do y <-
                      set_sc_obj_ref sc_yield_from_update sc_ptr
                       (Some ct_ptr);
                      y <-
                      set_tcb_obj_ref tcb_yield_to_update ct_ptr
                       (Some sc_ptr);
                      y <- tcb_sched_action tcb_sched_dequeue tcb_ptr;
                      y <- tcb_sched_action tcb_sched_enqueue tcb_ptr;
                      y <- tcb_sched_action tcb_sched_enqueue ct_ptr;
                      reschedule_required
                   od
           od
      else set_consumed sc_ptr args
    od
  \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac schedulable; clarsimp simp: bind_assoc)
   apply (wpsimp wp_del: tcb_sched_enqueue_valid_sched)
             apply (wpsimp wp: tcb_sched_enqueue_valid_sched)
            apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_sched_dequeue_valid_blocked_except_set)
           apply (wpsimp wp_del: tcb_sched_enqueue_valid_sched reschedule_valid_sched_const
                         wp: reschedule_required_valid_sched')
               apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)
              apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_enqueue)
             apply wpsimp
             apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs
                               tcb_sched_dequeue_valid_blocked_except_set)
            apply (wpsimp wp: set_tcb_yield_to_valid_sched set_sc_yield_from_valid_sched
                        cong: conj_cong imp_cong
                 | strengthen valid_sched_valid_ready_qs valid_sched_weak_valid_sched_action
                              valid_sched_valid_blocked)+
    apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift refill_unblock_check_st_tcb_at
                      refill_unblock_check_valid_sched is_schedulable_wp hoare_vcg_if_lift
                      sched_context_resume_valid_sched
                      sched_context_resume_ct_in_state[simplified ct_in_state_def]
                cong: conj_cong imp_cong
         | strengthen valid_sched_valid_ready_qs valid_sched_valid_sched_action
                      valid_sched_valid_blocked valid_sched_valid_release_q
                      valid_sched_ct_in_cur_domain)+
   apply (clarsimp simp: is_schedulable_bool_def ct_in_state_def active_sc_tcb_at_defs
                         valid_sched_def sc_tcb_sc_at_def not_cur_thread_def
                  split: option.splits dest!: get_tcb_SomeD)
   apply (intro conjI impI allI; fastforce?)
   apply clarsimp
   apply (drule invs_sym_refs)
   apply (frule_tac tp=tp in ARM.sym_ref_tcb_sc[where scp=sc_ptr], simp+)
  apply wpsimp
  done

(* end *)

crunches sched_context_resume
  for pred_tcb_at_ct[wp]: "\<lambda>s::det_state. pred_tcb_at P proj (cur_thread s) s"
  and active_sc_tcb_at_ct[wp]: "\<lambda>s::det_state. active_sc_tcb_at (cur_thread s) s"
  and budget_sufficient_ct[wp]: "\<lambda>s::det_state. budget_sufficient (cur_thread s) s"
  and budget_ready_ct[wp]: "\<lambda>s::det_state. budget_ready (cur_thread s) s"
    (wp: crunch_wps simp: crunch_simps)

lemma schedulable_sc_not_in_release_q:
  "\<lbrakk>\<forall>tp. bound_sc_tcb_at ((=) (Some scp)) tp s \<and> is_schedulable_bool tp (in_release_q tp s) s\<rbrakk>
       \<Longrightarrow> sc_not_in_release_q scp s"
  by (fastforce simp: is_schedulable_bool_def split: option.splits)

(* use valid blocked to argue that the thread must be in the ready qs *)
lemma sched_context_yield_to_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
       and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s)
       and ct_active and ct_ARS and valid_machine_time and invs\<rbrace>
   sched_context_yield_to sc_ptr args
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  unfolding sched_context_yield_to_def assert_opt_def
  apply (rule hoare_seq_ext[OF _ gscyf_sp])
  apply (rule hoare_seq_ext[OF _ sched_context_yield_to_valid_sched_helper])
  apply simp
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac sc_tcb_opt; clarsimp)
  apply (rename_tac tcb_ptr)
  apply (rule hoare_seq_ext[OF sched_context_yield_to_valid_sched_helper2])
  apply (wpsimp wp: sched_context_resume_ready_and_sufficient sched_context_resume_schedulable
                    sched_context_resume_valid_sched hoare_vcg_conj_lift
                    sched_context_resume_ct_in_state[simplified ct_in_state_def]
        | wps)+
  apply (clarsimp simp: sc_tcb_sc_at_def active_sc_tcb_at_defs
                 dest!: get_tcb_SomeD split: option.splits)
  apply (rename_tac tcb_ptr ko)
  apply (case_tac ko; clarsimp)
  apply (drule invs_sym_refs)
  apply (drule (2) sym_ref_sc_tcb, clarsimp)
  done

lemma invoke_sched_context_valid_sched:
  "\<lbrace>invs and valid_sched and valid_sched_context_inv iv and invs and simple_sched_action
      and valid_machine_time and (\<lambda>s. bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) (cur_thread s) s)
      and ct_active and ct_ARS\<rbrace>
     invoke_sched_context iv
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases iv; simp)
     by(wpsimp simp: invoke_sched_context_def
                 wp: sched_context_bind_tcb_valid_sched
                     sched_context_unbind_tcb_valid_sched sched_context_yield_to_valid_sched)+

lemma refill_update_cur_thread[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  unfolding refill_update_def
  by (wpsimp wp: set_object_wp get_object_wp simp: update_sched_context_def)

crunches set_refills, refill_update, refill_new
  for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at Q t s)"
  and etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"

lemma set_refills_sc_tcb_sc_at[wp]:
  "set_refills sc_ptr' refills \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp )
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma refill_update_sc_tcb_sc_at[wp]:
  "refill_update sc_ptr mrefills budget period \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding refill_update_def
  by (wpsimp wp: update_sched_context_wp refill_ready_wp)
     (fastforce simp: sc_tcb_sc_at_def obj_at_def)

lemma refill_new_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (fastforce simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma set_refills_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  apply fastforce
  done

lemma postpone_has_budget[wp]:
  "\<lbrace>has_budget tcbptr\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>rv. has_budget tcbptr :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  by (wpsimp simp: has_budget_equiv2
               wp: hoare_vcg_disj_lift get_sc_obj_ref_wp
                   tcb_release_enqueue_budget_sufficient tcb_release_enqueue_budget_ready)

lemma sched_context_resume_cond_has_budget':
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr
    and sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr
    and st_tcb_at runnable tcbptr
    and active_sc_tcb_at tcbptr\<rbrace>
   sched_context_resume (Some sc_ptr)
   \<lbrace>\<lambda>rv s :: det_state. not_in_release_q tcbptr s \<longrightarrow> has_budget tcbptr s \<rbrace>"
  unfolding sched_context_resume_def refill_ready_def
  apply (wpsimp wp: hoare_vcg_imp_lift')
               apply (simp add: not_in_release_q_simp[symmetric] del: not_in_release_q_simp)
  apply (wpsimp wp: hoare_vcg_imp_lift' thread_get_wp is_schedulable_wp postpone_in_release_q
                    refill_ready_wp refill_sufficient_wp
              simp: in_release_queue_in_release_q)+
  by (clarsimp simp: obj_at_def pred_tcb_at_def sc_at_pred_n_def active_sc_tcb_at_def
                     test_sc_refill_max_def has_budget_equiv2 sufficient_refills_defs
                     is_refill_sufficient_def is_refill_ready_def is_tcb
              dest!: is_schedulable_opt_Some
      | safe | fastforce)+

lemma refill_update_valid_blocked:
  "\<lbrace>valid_blocked and K (MIN_REFILLS \<le> mrefills) and sc_refills_sc_at (\<lambda>l. 1 \<le> length l) sc_ptr and
    test_sc_refill_max sc_ptr\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: set_object_wp get_object_wp refill_ready_wp
              simp: update_sched_context_def)
  apply (clarsimp simp: valid_blocked_def active_sc_tcb_at_defs st_tcb_at_kh_def sc_at_pred_n_def
                 split: option.splits
         | safe)+
      apply (drule_tac x=t in spec, simp)+
  done

lemma set_refills_budget_ready:
  "\<lbrace>budget_ready t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) t s \<longrightarrow>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs is_refill_ready_def split: option.splits
                  cong: conj_cong |safe)+
  apply (rule_tac x=scp in exI, clarsimp)
  done

lemma set_refills_budget_sufficient:
  "\<lbrace>budget_sufficient t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) t s \<longrightarrow>
                   MIN_BUDGET \<le> r_amount (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs is_refill_sufficient_def
                        sufficient_refills_def refills_capacity_def
                 split: option.splits
                  cong: conj_cong |safe)+
  apply fastforce
  done

lemma set_refills_valid_ready_qs:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ready_q tcb_ptr s \<longrightarrow>  (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  unfolding valid_ready_qs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_refills_budget_sufficient
                    set_refills_budget_ready simp: Ball_def)
  by (fastforce simp: in_ready_q_def)

lemma set_refills_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   not_queued tcb_ptr s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: set_refills_valid_ready_qs)
  apply (clarsimp simp: in_ready_q_def not_queued_def)
  done

(* FIXME: improve abstraction (ko_at_Endpoint could be simple_ko_at) *)
lemma set_refills_ep_at_pred[wp]:
  "set_refills sc_ptr refills \<lbrace>\<lambda>s. Q (ep_at_pred P p s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_def simple_obj_at_def split: if_splits)
  done

lemma set_refills_valid_ep_q:
  "\<lbrace>valid_ep_q and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ep_q tcb_ptr s \<longrightarrow>
                   (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                    r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ep_q\<rbrace>"
  unfolding valid_ep_q_def2
  apply (simp add: has_budget_equiv[simplified has_budget_def])
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_refills_budget_sufficient
                    hoare_vcg_disj_lift set_refills_budget_ready
              simp: Ball_def)
  apply (rename_tac s epptr tcbptr)
  apply (drule_tac x=epptr and y=tcbptr in spec2)
  apply (drule_tac x=tcbptr in spec, clarsimp)
  apply (safe; clarsimp simp: in_ep_q_def simple_obj_at_def pred_tcb_at_def obj_at_def)
  done

lemma set_refills_valid_sched_action:
  "\<lbrace>valid_sched_action and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   scheduler_action s = switch_thread tcb_ptr \<longrightarrow>  (MIN_BUDGET \<le> r_amount (hd refills) \<and>
                   r_time (hd refills) \<le> cur_time s + kernelWCET_ticks))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_action_def
  apply (wpsimp simp: is_activatable_def wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (wps, wp set_refills_pred_tcb_at)
   apply (wpsimp simp: weak_valid_sched_action_def
                   wp: hoare_vcg_all_lift hoare_vcg_imp_lift' set_refills_budget_sufficient
                       set_refills_budget_ready)
   apply (wpsimp simp: switch_in_cur_domain_def wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
   apply (wps, wpsimp)
  apply (clarsimp simp: switch_in_cur_domain_def weak_valid_sched_action_def)
  done

lemma refill_update_valid_ready_qs:
  "\<lbrace>valid_ready_qs and K (MIN_BUDGET \<le> budget) and K (0 < mrefills) and valid_machine_time\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  supply if_split [split del]
 unfolding refill_update_def refill_ready_def
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: update_sched_context_valid_ready_qs)
sorry
(*
        apply (wpsimp wp: set_refills_valid_ready_qs)
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply (wpsimp wp: is_round_robin_wp)
    apply (wpsimp wp: get_object_wp simp: update_sched_context_def set_object_def
      cong: conj_cong imp_cong)+
  apply (intro conjI impI allI; clarsimp split: if_splits simp: obj_at_def)
    apply (intro conjI impI allI)
      apply (clarsimp simp: valid_ready_qs_def)
      apply (drule_tac x=d and y=p in spec2, clarsimp)
      apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
      apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
      apply (intro conjI impI; fastforce?)
       apply (rule_tac x=scpb in exI, clarsimp)
       apply (clarsimp simp: sufficient_refills_def refills_capacity_def)
      apply (rule_tac x=scpb in exI, clarsimp)
      apply (clarsimp simp: cur_time_no_overflow)+ *)

(*  unfolding refill_update_def refill_ready_def
  apply (wpsimp wp: set_sched_context_valid_ready_qs_helper set_refills_valid_ready_qs
  hoare_vcg_all_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift' | wp update_sched_context_wp)+
apply (intro conjI impI allI)
apply (clarsimp split: if_splits)
apply (intro conjI)
apply clarsimp
     apply (erule cur_time_no_overflow)
  apply (clarsimp simp: obj_at_def in_ready_q_def)
    apply (subgoal_tac "budget_ready tcb_ptr s")
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
    apply_trace (clarsimp simp: valid_ready_qs_def)*)
(*
apply (clarsimp split: if_splits)
subgoal

apply (clarsimp split: if_splits)
apply (intro conjI impI)
prefer 2
  apply (clarsimp simp: obj_at_def in_ready_q_def)
    apply (subgoal_tac "budget_ready tcb_ptr s")
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)
    apply_trace (clarsimp simp: valid_ready_qs_def)

  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
apply (clarsimp simp: refill_ready_def bind_assoc)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
apply clarsimp
  apply (clarsimp simp: obj_at_def in_ready_q_def )
apply (clarsimp split: if_splits)
apply (intro conjI impI allI)

apply (wpsimp wp: set_sched_context_valid_ready_qs_helper)
     apply (erule cur_time_no_overflow)

apply (wpsimp wp: set_sched_context_valid_ready_qs_helper)
subgoal sorry

apply (wpsimp wp: set_sched_context_valid_ready_qs_helper)
     apply (erule cur_time_no_overflow)

apply (wpsimp wp: set_sched_context_valid_ready_qs_helper)
subgoal sorry


apply (wpsimp wp: set_sched_context_valid_ready_qs_helper set_refills_valid_ready_qs)
    apply (subgoal_tac "budget_ready tcb_ptr s")
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def in_ready_q_def in_queue_2_def)
    apply_trace (clarsimp simp: valid_ready_qs_def)





apply (rule_tac new_time="cur_time s" in set_sched_context_valid_ready_qs_helper)
apply (wpsimp wp: set_sched_context_valid_ready_qs_helper[where new_time="cur_time sa"])
  apply (wpsimp wp: set_sched_context_valid_ready_qs_helper set_refills_valid_ready_qs
  hoare_vcg_all_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift' simp: is_round_robin_def refill_ready_def | wp update_sched_context_wp)+
  apply (clarsimp simp: obj_at_def in_ready_q_def )
  apply (intro conjI; intro impI allI; clarsimp)
   apply (intro conjI; intro impI allI; clarsimp?)
    apply (clarsimp split: if_splits; safe)
     apply (erule cur_time_no_overflow)
    apply (subgoal_tac "budget_ready tcb_ptr s")
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def)

    apply (clarsimp simp: valid_ready_qs_def)
    apply (drule_tac x=d and y=p in spec2, clarsimp)
    apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
    apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
    apply (intro conjI impI; fastforce?)
     apply (rule_tac x=scpb in exI, clarsimp)
     apply (clarsimp simp: sufficient_refills_def refills_capacity_def)
    apply (rule_tac x=scpb in exI, clarsimp)
    apply (clarsimp simp: cur_time_no_overflow)+
   apply (intro conjI impI allI)
     apply (clarsimp simp: valid_ready_qs_def)
     apply (drule_tac x=d and y=p in spec2, clarsimp)
     apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
     apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
     apply (intro conjI impI; fastforce?)
    apply (clarsimp simp: in_queue_2_def pred_tcb_at_def obj_at_def split: if_splits)
    apply (clarsimp simp: valid_ready_qs_def)
    apply (drule_tac x=d and y=p in spec2, clarsimp)
    apply (drule_tac x=tcb_ptr in bspec, simp, clarsimp split: if_splits)
    apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
   apply (clarsimp simp: valid_ready_qs_def)
   apply (drule_tac x=d and y=p in spec2, clarsimp)
   apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
   apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
   apply (intro conjI impI; fastforce)
  apply (intro conjI impI allI)
   apply (clarsimp simp: valid_ready_qs_def)
   apply (drule_tac x=d and y=p in spec2, clarsimp)
   apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
   apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
   apply (intro conjI impI; fastforce?)
    apply (rule_tac x=scpb in exI, clarsimp)
    apply (clarsimp simp: sufficient_refills_def refills_capacity_def)
   apply (rule_tac x=scpb in exI, clarsimp)
   apply (clarsimp simp: cur_time_no_overflow)+
  apply (clarsimp simp: valid_ready_qs_def) *)
(*
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=t in bspec, simp, clarsimp split: if_splits)
  apply (clarsimp simp: etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs
      split: if_splits option.splits)
  apply (intro conjI impI; fastforce?)
  done*)

(* FIXME: check if used *)
lemma refill_update_valid_release_q_not_in_release_q:
  "\<lbrace>valid_release_q and K (0 < mrefills)
       and (\<lambda>s.\<forall>t\<in>set (release_queue s). bound_sc_tcb_at (\<lambda>p. p \<noteq> Some sc_ptr) t s)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: is_round_robin_wp update_sched_context_wp  refill_ready_wp
                    set_refills_valid_release_q_not_in_release_q)
  apply (intro conjI impI allI; clarsimp simp: valid_release_q_def sc_refills_sc_at_def obj_at_def; rule conjI)
             by (fastforce simp: active_sc_tcb_at_defs st_tcb_at_kh_def not_in_release_q_def
                          split: if_splits,
                (clarsimp simp: sorted_release_q_def active_sc_tcb_at_defs elim!: sorted_wrt_mono_rel[rotated];
               ((frule_tac x=x in bspec, simp, drule_tac x=y in bspec, simp)+);
                 fastforce simp: tcb_ready_time_kh_def tcb_ready_time_def get_tcb_def
                          dest!: get_tcb_SomeD split: option.splits))+

lemma refill_update_valid_release_q_not_in_release_q':
  "\<lbrace>valid_release_q and K (0 < mrefills)
       and sc_not_in_release_q sc_ptr\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: is_round_robin_wp refill_ready_wp update_sched_context_wp
                    set_refills_valid_release_q_not_in_release_q)
apply (drule (1) sc_not_in_release_q_imp_not_linked[rotated])
  apply (intro conjI impI allI; clarsimp simp: valid_release_q_def sc_refills_sc_at_def obj_at_def; rule conjI)
             by (fastforce simp: active_sc_tcb_at_defs st_tcb_at_kh_def not_in_release_q_def
                          split: if_splits,
                (clarsimp simp: sorted_release_q_def active_sc_tcb_at_defs elim!: sorted_wrt_mono_rel[rotated];
               ((frule_tac x=x in bspec, simp, drule_tac x=y in bspec, simp)+);
                 fastforce simp: tcb_ready_time_kh_def tcb_ready_time_def get_tcb_def
                          dest!: get_tcb_SomeD split: option.splits))+

lemma refill_update_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   refill_update sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: is_round_robin_wp update_sched_context_wp refill_ready_wp
                    set_refills_valid_sched_action)
  apply (clarsimp simp: valid_sched_action_def; intro conjI impI)
     by (clarsimp simp: obj_at_def is_activatable_def weak_valid_sched_action_def
                        simple_sched_action_def switch_in_cur_domain_def
                 split: scheduler_action.splits
        | safe
        | clarsimp simp: st_tcb_at_kh_def obj_at_kh_def pred_tcb_at_def obj_at_def)+

lemma refill_update_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>tcb_ptr.  bound_sc_tcb_at (\<lambda>t. t = (Some sc_ptr)) tcb_ptr s \<longrightarrow> tcb_ptr \<in> S)\<rbrace>
   refill_update sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding refill_update_def
  by (wpsimp wp: is_round_robin_wp hoare_vcg_imp_lift' hoare_vcg_all_lift refill_ready_wp
                 update_sched_context_valid_blocked_except_set_except hoare_vcg_if_lift2 |
      wp update_sched_context_wp)+

lemma update_sched_context_valid_ready_qs_helper2:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ready_q tcb_ptr s \<longrightarrow>
                   (0 < mrefills) \<and>
                   MIN_BUDGET \<le> r_amount refill \<and>
                   r_time refill \<le> cur_time s + kernelWCET_ticks)\<rbrace>
   update_sched_context sc_ptr (\<lambda>sc. sc \<lparr>sc_period := period, sc_refills := [refill],
                                sc_refill_max := mrefills, sc_budget := budget\<rparr>)
   \<lbrace>\<lambda>r. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_ready_qs_def active_sc_tcb_at_defs st_tcb_at_kh_def not_queued_def
                        etcb_defs refill_sufficient_kh_def  refill_ready_kh_def is_refill_sufficient_def is_refill_ready_def
                        refills_capacity_def sufficient_refills_def bound_sc_tcb_at_kh_def in_ready_q_def
                  cong: conj_cong imp_cong
                 split: if_splits option.splits)
  apply (drule_tac x=d in spec, drule_tac x=p in spec, clarsimp, drule (1) bspec, clarsimp)
  apply (drule_tac x=t in spec, clarsimp)
  apply (case_tac y; simp)
  apply (safe; fastforce)
  done

lemma refill_new_valid_ready_qs:
  "\<lbrace>valid_ready_qs and K (MIN_BUDGET \<le> budget) and K (0 < mrefills) and valid_machine_time\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  supply if_split [split del]
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_valid_ready_qs_helper2 set_refills_valid_ready_qs
                    hoare_vcg_all_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift' | wp update_sched_context_wp )+
  apply (clarsimp simp: obj_at_def in_ready_q_def)
  by (erule cur_time_no_overflow)

lemma update_sc_consumed_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>
   update_sched_context csc (sc_consumed_update (\<lambda>_. consumed))
   \<lbrace>\<lambda>_ s:: det_state. P (active_sc_tcb_at t s) \<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                        test_sc_refill_max_def
                  cong: conj_cong imp_cong split: option.splits)
  apply fastforce
  done

lemma update_sc_consumed_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>
   update_sched_context csc (sc_consumed_update (\<lambda>_. consumed))
   \<lbrace>\<lambda>_ s:: det_state. P (budget_sufficient t s) \<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def
                  cong: conj_cong imp_cong split: option.splits)
  apply fastforce
  done

lemma update_sc_consumed_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>
   update_sched_context csc (sc_consumed_update (\<lambda>_. consumed))
   \<lbrace>\<lambda>_ s:: det_state. P (budget_ready t s) \<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def
                  cong: conj_cong imp_cong split: option.splits)
  apply fastforce
  done

lemma update_sched_context_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q scp\<rbrace>
     update_sched_context ref new \<lbrace>\<lambda>_. sc_not_in_release_q scp\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def split: if_splits)

lemma refill_new_valid_release_q:
  "\<lbrace>valid_release_q and K (0 < mrefills) and sc_not_in_release_q sc_ptr\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding refill_new_def
  by (wpsimp wp: set_refills_valid_release_q_not_in_release_q hoare_drop_imp
                 round_robin_inv hoare_vcg_if_lift2
                 update_sched_context_valid_release_q_not_in_release_q)

lemma refill_new_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: is_round_robin_wp update_sched_context_wp set_refills_valid_sched_action)
  by (clarsimp simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def simple_sched_action_def
                   switch_in_cur_domain_def
    | clarsimp simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def pred_tcb_at_def
    | safe)+

lemma refill_new_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>t. t = (Some sc_ptr)) tcb_ptr s \<longrightarrow> tcb_ptr \<in> S)\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding refill_new_def set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_blocked_except_set_def obj_at_def st_tcb_at_kh_eq_commute)
  apply safe
  by (clarsimp simp: active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_def obj_at_kh_def
                     test_sc_refill_max_kh_def st_tcb_at_kh_def
                     active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def
              split: option.splits if_splits
    | drule_tac x=t in spec)+

lemma refill_update_test_sc_refill_max[wp]:
  "\<lbrace>K (P (x2 > 0))\<rbrace>
   refill_update sc_ptr x1 budget x2
   \<lbrace>\<lambda>rv s. P (test_sc_refill_max sc_ptr s)\<rbrace>"
  unfolding refill_update_def
  by (wpsimp simp: set_refills_def wp: update_sched_context_wp refill_ready_wp)
     (clarsimp simp: sc_tcb_sc_at_def obj_at_def test_sc_refill_max_def)

lemma refill_new_test_sc_refill_max:
  "\<lbrace>K (P (x1 > 0))\<rbrace>
     refill_new sc_ptr x1 budget x2
   \<lbrace>\<lambda>rv s. P (test_sc_refill_max sc_ptr s)\<rbrace>"
  unfolding refill_new_def
  by (wpsimp simp: set_refills_def wp: update_sched_context_wp)
     (clarsimp simp: sc_tcb_sc_at_def obj_at_def test_sc_refill_max_def)

crunches refill_update, refill_new, set_refills
  for ct_in_cur_domain[wp]: ct_in_cur_domain
  and ct_not_in_q[wp]: ct_not_in_q
  and pred_tcb_at[wp]: "pred_tcb_at proj test ptr"
  and not_queued[wp]: "not_queued ptr"
  and not_in_release_q[wp]: "not_in_release_q ptr"
  and valid_idle_etcb[wp]: valid_idle_etcb
  (wp: crunch_wps simp: crunch_simps)
(*
crunches commit_domain_time, refill_budget_check
  for sc_tcb_sc_at[wp]: "sc_tcb_sc_at P sc_ptr"
  and valid_release_q[wp]: "valid_release_q"
  and valid_sched_action[wp]: "valid_sched_action"
  and weak_valid_sched_action[wp]: "weak_valid_sched_action"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain"
  and valid_idle_etcb[wp]: valid_idle_etcb
  (wp: crunch_wps simp: crunch_simps)
*)
lemma refill_budget_check_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) tcb_ptr s \<longrightarrow>
                   not_queued tcb_ptr s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_def refill_full_def
  supply if_split [split del]
  by (wpsimp wp: set_refills_valid_ready_qs_not_queued  is_round_robin_wp refill_ready_wp
           simp: Let_def)

lemma set_refills_valid_blocked_except_set[wp]:
  "set_refills sc_ptr refills \<lbrace>valid_blocked_except_set S\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (auto simp: valid_blocked_except_set_def active_sc_tcb_at_defs st_tcb_at_kh_def)
  done

crunches commit_domain_time, refill_budget_check
  for valid_blocked_except_set[wp]: "valid_blocked_except_set S"
  and valid_blocked[wp]: "valid_blocked"
  (wp: crunch_wps simp: crunch_simps)

lemma commit_time_sc_tcb_sc_at[wp]:
  "commit_time \<lbrace>\<lambda>s. sc_tcb_sc_at P sc_ptr s\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps)

lemma reply_push_sc_tcb_sc_at:
  "reply_push caller callee reply_ptr False \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: hoare_drop_imps)

lemma make_arch_fault_msg_obj_at_sc_tcb_sc_at[wp]:
  "make_arch_fault_msg a b \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P p s)\<rbrace>"
  by (wpsimp simp: sc_tcb_sc_at_def wp: make_arch_fault_msg_obj_at)

crunches possible_switch_to, do_ipc_transfer, postpone, refill_full
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P p s)"
  (wp: crunch_wps)

lemma send_ipc_sc_tcb_sc_at:
  "send_ipc block call badge can_grant False thread epptr \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding send_ipc_def
  by (wpsimp wp: hoare_drop_imps reply_push_sc_tcb_sc_at get_simple_ko_wp hoare_vcg_all_lift)

lemma send_fault_ipc_sc_tcb_sc_at:
  "send_fault_ipc tptr handler_cap fault False \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding send_fault_ipc_def
  by (wpsimp wp: hoare_drop_imps reply_push_sc_tcb_sc_at send_ipc_sc_tcb_sc_at)

lemma sc_refills_update_sc_tcb_sc_at[wp]:
  "update_sched_context csc_ptr (sc_refills_update a) \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  by (wpsimp wp: update_sched_context_sc_at_pred_n_indep)

lemma check_budget_sc_tcb_sc_at[wp]:
  "check_budget \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  supply if_split [split del]
  unfolding check_budget_def charge_budget_def end_timeslice_def
            handle_timeout_def refill_budget_check_def
  apply clarsimp
  apply (wpsimp wp: hoare_drop_imps send_fault_ipc_sc_tcb_sc_at hoare_vcg_if_lift2 simp: Let_def)
  done

lemma commit_time_valid_release_q:
  "\<lbrace>valid_release_q and
    (\<lambda>s. \<forall>t. bound_sc_tcb_at (\<lambda>t. t = Some (cur_sc s)) t s
             \<longrightarrow> not_in_release_q t s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
 (*  by (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps
                  set_refills_valid_release_q)*) sorry

lemma commit_time_valid_ready_qs:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>t. bound_sc_tcb_at (\<lambda>t. t = Some (cur_sc s)) t s
             \<longrightarrow> not_queued t s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   apply (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps
                  set_refills_valid_ready_qs refill_budget_check_valid_ready_qs_not_queued)
   apply (fastforce simp: in_queue_2_def not_queued_def)
   done

lemma commit_time_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                  hoare_vcg_all_lift hoare_drop_imps set_refills_valid_sched_action_act_not
                  refill_budget_check_valid_sched_action_act_not)

lemma commit_time_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                     hoare_vcg_all_lift hoare_drop_imps)

lemma commit_time_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_idle_etcb :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: update_sched_context_valid_sched_action_simple_sched_action
                     hoare_vcg_all_lift hoare_drop_imps)

lemma commit_time_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_blocked_except_set S :: det_state \<Rightarrow> _\<rbrace>"
   unfolding commit_time_def sc_refill_ready_def
   by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps update_sched_context_valid_blocked_except_set)

lemma commit_time_valid_sched:
  "\<lbrace>valid_sched and
    simple_sched_action and
    (\<lambda>s. \<forall>t. bound_sc_tcb_at (\<lambda>t. t = Some (cur_sc s)) t s \<longrightarrow> not_queued t s \<and> not_in_release_q t s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
   unfolding valid_sched_def
   by (wpsimp wp: commit_time_valid_release_q
                  commit_time_valid_sched_action commit_time_ct_in_cur_domain
                  commit_time_valid_idle_etcb commit_time_valid_blocked_except_set
                  commit_time_valid_ready_qs)

lemma check_budget_simple_sched_action[wp]:
  "check_budget \<lbrace>simple_sched_action\<rbrace>"
  unfolding check_budget_def charge_budget_def
  apply clarsimp
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_if_lift2
              simp: Let_def refill_budget_check_def refill_full_def)
  done

lemma set_thread_state_runnable:
  "\<lbrace>tcb_at tcbptr and K (runnable st)\<rbrace>
   set_thread_state tcbptr st
   \<lbrace>\<lambda>rv. st_tcb_at runnable tcbptr\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: set_object_wp, clarsimp simp: pred_tcb_at_def obj_at_def)

(* charge_budget *)

lemma end_timeslice_valid_sched_subset:
  "\<lbrace>valid_release_q and valid_ready_qs and
    weak_valid_sched_action and valid_blocked and valid_idle_etcb and valid_ep_q and
    ct_not_in_release_q and ct_not_queued and scheduler_act_sane and invs and ct_active
    and cur_sc_chargeable
    and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. (valid_release_q and valid_ready_qs and
         weak_valid_sched_action and valid_blocked and valid_idle_etcb)::det_state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def handle_timeout_def send_fault_ipc_def
  apply wpsimp
                          apply (wpsimp wp: send_ipc_valid_sched_subset_for_handle_timeout[simplified conj_assoc pred_conj_def])
                         apply (wpsimp wp: tcb_sched_append_valid_blocked_except_set_const)+
          apply (wpsimp wp: postpone_valid_release_q postpone_valid_ready_qs
                            postpone_weak_valid_sched_action postpone_valid_blocked
                            gts_wp)+
  apply (subgoal_tac "bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s")
   apply (clarsimp dest!: get_tcb_SomeD
                    simp: is_tcb ct_in_state_def cur_sc_tcb_def
                          sc_at_pred_n_def schact_is_rct_def runnable_eq_active
                          budget_sufficient_defs budget_ready_defs active_sc_tcb_at_defs)
   apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. x = Some (cur_thread s)) (cur_sc s) s")
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
   apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl, symmetric], clarsimp)
   apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: cur_sc_chargeable_def pred_tcb_at_def obj_at_def active_sc_tcb_at_defs
                 dest!: get_tcb_SomeD)
  done

lemma refill_budget_check_st_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: is_round_robin_wp refill_ready_wp refill_full_wp)

lemma refill_budget_check_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q scp\<rbrace> refill_budget_check usage \<lbrace>\<lambda>_. sc_not_in_release_q scp\<rbrace>"
   by (wpsimp wp: set_refills_ct_not_in_release_q hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma refill_budget_check_sc_scheduler_act_not[wp]:
  "\<lbrace>sc_scheduler_act_not scp\<rbrace> refill_budget_check usage \<lbrace>\<lambda>_. sc_scheduler_act_not scp\<rbrace>"
   by (wpsimp wp: set_refills_ct_not_in_release_q hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma refill_budget_check_valid_release_q:
  "\<lbrace>valid_release_q and (\<lambda>s. sc_not_in_release_q (cur_sc s) s)\<rbrace>
  refill_budget_check consumed
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding refill_budget_check_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  by (wpsimp simp: refill_full_def
               wp: update_sched_context_valid_release_q_not_in_release_q
                   refill_budget_check_valid_release_q_not_in_release_q
                   set_refills_valid_release_q_not_in_release_q
                   hoare_drop_imp|wps)+

lemma set_refills_in_ep_q[wp]:
  "set_refills sc_ptr x1 \<lbrace>\<lambda>s. P (in_ep_q t s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp simp: Let_def)
  apply (erule subst[where P=P, rotated])
  apply (clarsimp simp: in_ep_q_def obj_at_def)
  apply (rule iffI; clarsimp; rule_tac x=ptr in exI; clarsimp)
  done

lemma refill_budget_check_in_ep_q[wp]:
  "refill_budget_check x1 \<lbrace>\<lambda>s. P (in_ep_q t s)\<rbrace>"
  supply if_split [split del]
  unfolding refill_budget_check_def
  by (wpsimp simp: Let_def wp: is_round_robin_wp refill_ready_wp refill_full_wp)

lemma refill_budget_check_valid_ep_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. sc_not_in_ep_q (cur_sc s) s)\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  supply if_split [split del]
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_valid_ep_q is_round_robin_wp refill_ready_wp refill_full_wp
           simp: Let_def)
     (fastforce simp: pred_tcb_at_def obj_at_def)

lemma refill_budget_check_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_weak_valid_sched_action_act_not
                 is_round_robin_wp refill_ready_wp refill_full_wp
           simp: Let_def)

crunches refill_full
  for valid_read_qs[wp]: valid_ready_qs
  and not_queued[wp]: "not_queued t"

lemma refill_budget_check_valid_ready_qs:
  "\<lbrace>valid_ready_qs\<rbrace>
   refill_budget_check consumed capacity
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: refill_full_def
               wp: update_sched_context_valid_ready_qs
                   refill_budget_check_valid_ready_qs
                   set_refills_valid_ready_qs_not_queued
                   hoare_drop_imp|wps)+
  sorry (* waiting for the spec update; will need more preconditions *)

lemma refill_budget_check_valid_ep_q:
  "\<lbrace>valid_ep_q and (\<lambda>s. sc_not_in_ep_q (cur_sc s) s)\<rbrace>
   refill_budget_check consumed capacity
   \<lbrace>\<lambda>_. valid_ep_q\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: refill_split_check_valid_ep_q hoare_drop_imp
                    set_refills_valid_ep_q_not_in_ep_q
                    update_sched_context_valid_ep_q_not_in_ep_q
              simp: refill_full_def
         | wps)+
  done

lemma refill_budget_check_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check consumed capacity
   \<lbrace>\<lambda>_. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: update_sched_context_weak_valid_sched_action_act_not
                 refill_split_check_weak_valid_sched_action hoare_drop_imp
                 set_refills_weak_valid_sched_action_act_not
           simp: refill_full_def|wps)+

lemma refill_budget_check_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: update_sched_context_valid_blocked
                 is_round_robin_wp refill_ready_wp refill_full_wp
           simp: refill_full_def)

lemma refill_budget_check_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: is_round_robin_wp refill_ready_wp refill_full_wp)

lemma refill_budget_check_ct_not_in_q:
  "\<lbrace>ct_not_in_q\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: is_round_robin_wp refill_ready_wp refill_full_wp)

lemma refill_budget_check_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: is_round_robin_wp refill_ready_wp refill_full_wp)


lemma refill_budget_check_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)
       and (\<lambda>s. sc_not_in_release_q (cur_sc s) s) and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  apply (wpsimp wp: refill_budget_check_valid_ready_qs refill_budget_check_valid_release_q
                    refill_budget_check_ct_in_cur_domain refill_budget_check_valid_sched_action_act_not
                    refill_budget_check_valid_idle_etcb refill_budget_check_ct_not_in_q
                    refill_budget_check_valid_blocked)
  done

lemma in_queue_valid_ready_qs_dest:
  "in_queue_2 (ready_queues s d p) t \<Longrightarrow>
   valid_ready_qs s \<Longrightarrow>
      (etcb_at (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) t s \<and>
       st_tcb_at_kh runnable t (kheap s) \<and>
       active_sc_tcb_at_kh t (kheap s) \<and>
       budget_sufficient_kh t (kheap s) \<and>
       budget_ready_kh (cur_time s) t (kheap s))"
  apply (clarsimp simp: valid_ready_qs_def)
  apply (clarsimp simp: in_queue_2_def)
  done

crunches refill_budget_check
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
  (wp: crunch_wps simp: crunch_simps)

lemma refill_budget_check_cur_sc_tcb[wp]:
  "refill_budget_check usage \<lbrace>cur_sc_tcb\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps
           simp: refill_full_def Let_def)

lemma refill_budget_check_active_sc_tcb_at[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: active_sc_tcb_at_update_sched_context_no_change
                 is_round_robin_wp refill_ready_wp refill_full_wp)

lemma invoke_untyped_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  by (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)

lemma invoke_untyped_oe[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  by (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)+

crunches cap_delete
  for scheduler_act_sane[wp]: " scheduler_act_sane :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma cap_delete_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   cap_delete x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace>
  cap_delete x
   -, \<lbrace>\<lambda>rv. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_def by wpsimp+

lemma set_tcb_obj_ref_ct_in_state_no_change:
  "(\<And>y. P (tcb_state y) \<Longrightarrow> P (tcb_state (f (\<lambda>_. new) y))) \<Longrightarrow>
   set_tcb_obj_ref f ref new \<lbrace>ct_in_state P:: det_state \<Rightarrow> _\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma preemption_point_ct_in_state[wp]:
  "preemption_point \<lbrace>ct_in_state P:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: preemption_point_inv; clarsimp simp: ct_in_state_def)

crunches finalise_cap
  for ct_not_blocked[wp]: "ct_not_blocked :: det_state \<Rightarrow> _"
  (ignore: set_tcb_obj_ref
       wp: crunch_wps set_thread_state_ct_in_state set_tcb_obj_ref_ct_in_state_no_change thread_set_ct_in_state maybeM_inv)

crunches cap_swap_ext, cap_delete
  for ct_not_blocked[wp]: "ct_not_blocked :: det_state \<Rightarrow> _"
  (wp: crunch_wps dxo_wp_weak)

lemmas rec_del_invs''_CTEDeleteCall = rec_del_invs''
                                      [where call = "(CTEDeleteCall x True)" for x,
                                       simplified,
                                       simplified pred_conj_def,
                                       THEN use_specE']

lemma cap_delete_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable and ct_not_blocked and valid_ep_q and valid_ntfn_q and invs \<rbrace>
   cap_delete x
   \<lbrace>\<lambda>rv. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_def
  apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and ct_not_blocked and valid_ep_q and valid_ntfn_q and invs "
                  in hoare_strengthen_post)
  apply (wpsimp wp: rec_del_invs''_CTEDeleteCall
                    [where Q="cur_sc_chargeable and ct_not_blocked and valid_ep_q and valid_ntfn_q",
                     simplified]
                    preemption_point_inv finalise_cap_valid_ipc_q)
  apply (clarsimp simp: ct_in_state_def)+
  done

lemma cap_revoke_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   cap_revoke a
  \<lbrace>\<lambda>rv. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule validE_valid, rule cap_revoke_preservation)
    apply (wpsimp wp: preemption_point_inv cap_delete_valid_ipc_q)+
  done

crunches cap_insert, sched_context_unbind_tcb, sched_context_bind_tcb, set_priority, set_mcpriority
  for scheduler_act_sane[wp]: "scheduler_act_sane :: det_state \<Rightarrow> _"
  (wp: crunch_wps tcb_release_remove_not_in_release_q')

lemma tcb_release_enqueue_not_in_release_q:
  "\<lbrace>not_in_release_q t' and (\<lambda>s. t \<noteq> t')\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>rv. not_in_release_q t'\<rbrace>"
  unfolding tcb_release_enqueue_def
  apply wpsimp
     apply (rule_tac Q="\<lambda>_ _. not_in_release_q_2 (qs) t' \<and> (t \<noteq> t')" in hoare_strengthen_post[rotated])
      apply (fastforce simp: not_in_release_q_def dest: in_set_zip1)
     apply wpsimp+
  done

lemma tcb_release_enqueue_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and (\<lambda>s. tcb_ptr \<noteq> cur_thread s)\<rbrace>
   tcb_release_enqueue tcb_ptr
   \<lbrace>\<lambda>xa. ct_not_in_release_q\<rbrace>"
  unfolding postpone_def
  apply (rule hoare_weaken_pre, wps)
  apply (wpsimp wp: tcb_release_enqueue_not_in_release_q)+
  done

lemma postpone_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and (\<lambda>s. sc_tcb_sc_at (\<lambda>x. x \<noteq> Some (cur_thread s)) x2a s)\<rbrace>
   postpone x2a
   \<lbrace>\<lambda>xb. ct_not_in_release_q\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: get_sc_obj_ref_wp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def )
  done

crunches install_tcb_cap
  for scheduler_act_sane[wp]: "scheduler_act_sane :: det_state \<Rightarrow> _"
  and ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
  and ct_not_in_release_q[wp]: "ct_not_in_release_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps preemption_point_inv ignore: check_cap_at simp: check_cap_at_def)

lemma install_tcb_cap_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked and valid_ep_q and valid_ntfn_q\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>rv. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv)

lemma invoke_tcb_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   invoke_tcb x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac x; simp)
         defer 7
         defer 4
         apply wpsimp+
   apply (case_tac x82; wpsimp)
  apply (wpsimp)
  apply (wpsimp wp: hoare_drop_imps install_tcb_cap_valid_ipc_q simp: install_tcb_frame_cap_def)+
  done

lemma invoke_tcb_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_tcb x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q \<rbrace>
   invoke_tcb x
   -, \<lbrace>\<lambda>rv. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  subgoal
  apply (case_tac x; simp)
           prefer 8
           apply (case_tac x82; wpsimp)
          apply (wpsimp simp: install_tcb_frame_cap_def | wpsimp wp: hoare_drop_imps)+
  done
  subgoal
  apply (case_tac x; simp)
           prefer 8
           apply (case_tac x82; wpsimp)
          apply (wpsimp wp: install_tcb_cap_valid_ipc_q simp: install_tcb_frame_cap_def | wpsimp wp: hoare_drop_imps)+
  done
  done

crunches install_tcb_cap
  for ct_not_blocked[wp]: "ct_not_blocked :: det_state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv)

lemma install_tcb_frame_cap_ctcscb:
  "\<lbrace>invs and cur_sc_chargeable and
            ct_not_blocked and valid_ep_q and valid_ntfn_q\<rbrace>
      install_tcb_frame_cap t sl buf
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_frame_cap_def
  by wpsimp

lemma tcc_cur_sc_chargeable:
  "\<lbrace>invs and tcb_inv_wf (ThreadControlCaps t sl fh th croot vroot buf)
    and cur_sc_chargeable and ct_not_blocked
    and valid_ep_q and valid_ntfn_q\<rbrace>
   invoke_tcb (ThreadControlCaps t sl fh th croot vroot buf)
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  supply if_cong[cong]
  apply (simp add: split_def cong: option.case_cong)
  apply wp
  \<comment> \<open>install_tcb_cap 2\<close>
       apply (wpsimp wp: install_tcb_frame_cap_ctcscb)
      apply (simp)
      \<comment> \<open>install_tcb_cap 1\<close>
      apply (rule hoare_vcg_E_elim, wp)
      apply (wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                        install_tcb_cap_invs install_tcb_cap_valid_ipc_q)
     \<comment> \<open>install_tcb_cap 0\<close>
     apply (simp)
     apply (rule hoare_vcg_E_elim, wp)
     apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                        install_tcb_cap_invs install_tcb_cap_valid_ipc_q
            | strengthen tcb_cap_always_valid_strg
            | wp install_tcb_cap_cte_wp_at_ep)+)[1]
    \<comment> \<open>install_tcb_cap 4\<close>
    apply (simp)
    apply (rule hoare_vcg_E_elim, wp)
    apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                       install_tcb_cap_invs install_tcb_cap_valid_ipc_q
           | strengthen tcb_cap_always_valid_strg
           | wp install_tcb_cap_cte_wp_at_ep)+)[1]
   \<comment> \<open>install_tcb_cap 3\<close>
   apply (simp)
   apply (rule hoare_vcg_E_elim, wp)
   apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                      install_tcb_cap_invs install_tcb_cap_valid_ipc_q
          | strengthen tcb_cap_always_valid_strg
          | wp install_tcb_cap_cte_wp_at_ep)+)[1]
  \<comment> \<open>cleanup\<close>
  apply (simp)
  apply (strengthen tcb_cap_always_valid_strg)
  apply (clarsimp cong: conj_cong)
  \<comment> \<open>resolve generated preconditions\<close>
  apply (intro conjI impI;
         clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                 dest!: valid_vtable_root_is_arch_cap)
      apply (all \<open>clarsimp simp: is_cap_simps cte_wp_at_caps_of_state\<close>)
     apply (all \<open>clarsimp simp: obj_at_def is_tcb typ_at_eq_kheap_obj cap_table_at_typ\<close>)
  by auto

lemma invoke_tcb_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and tcb_inv_wf x and
   ct_not_blocked and valid_ep_q and valid_ntfn_q\<rbrace>
   invoke_tcb x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac x)
  defer 5
  defer 4
    apply wpsimp+
    apply (case_tac x82; wpsimp)
    apply (wpsimp+)[2]
  apply (wpsimp wp: tcc_cur_sc_chargeable[simplified])
  done

lemma invoke_domain_no_exception[wp]:
  "\<lbrace>\<top>\<rbrace>
   invoke_domain x61 x62
   -, \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: invoke_domain_def)+

lemma cap_revoke_ct_not_queued:
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q \<rbrace>
   cap_revoke (a, b)
   \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  "cap_revoke (a, b) \<lbrace>ct_not_in_release_q :: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked  and valid_ntfn_q and valid_ep_q\<rbrace>
   cap_revoke (a, b)
   \<lbrace>\<lambda>_. cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  subgoal
  apply (rule hoare_strengthen_post, rule cap_revoke_preservation2)
  apply (wpsimp wp: preemption_point_inv cap_delete_valid_ipc_q)+
  done
  subgoal
  apply (rule hoare_strengthen_post, rule cap_revoke_preservation2)
  apply (wpsimp wp: preemption_point_inv)+
  done
  subgoal
  apply (rule hoare_strengthen_post, rule cap_revoke_preservation2)
  apply (wpsimp wp: preemption_point_inv cap_delete_valid_ipc_q)+
  apply (clarsimp simp: ct_in_state_def)+
  done
  done

lemma cap_revoke_cur_thread_conditions:
  "\<lbrace>ct_not_queued and ct_not_in_release_q
    and cur_sc_chargeable and scheduler_act_sane
    and valid_ntfn_q and valid_ep_q and invs and ct_not_blocked\<rbrace>
   cap_revoke (a, b)
   \<lbrace>\<lambda>rv. ct_not_queued and ct_not_in_release_q and cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post, rule cap_revoke_preservation2)
    apply (wpsimp wp: preemption_point_inv cap_delete_valid_ipc_q)+
     apply (clarsimp simp: ct_in_state_def)+
  done

lemma invoke_cnode_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued and scheduler_act_sane and valid_ntfn_q and valid_ep_q\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked and valid_ntfn_q and valid_ep_q\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  supply if_splits [split del]
  by (wpsimp wp: cap_revoke_ct_not_queued simp: invoke_cnode_def)+

lemma invoke_cnode_scheduler_act_sane_new:
  "\<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_chargeable
    and scheduler_act_sane and valid_ntfn_q and valid_ep_q and invs and ct_not_blocked\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. ct_not_queued and ct_not_in_release_q and cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  supply if_splits [split del]
  apply (wpsimp wp: cap_revoke_cur_thread_conditions cap_delete_ct_not_queued simp: invoke_cnode_def)+
  apply (rule valid_validE_E)
  apply wpsimp+
  done

lemma invoke_irq_control_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. ct_not_queued:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q:: det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>cur_sc_chargeable\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac x; wpsimp)
  apply (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)
  apply (case_tac x; wpsimp)
  apply (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)
  apply (case_tac x; wpsimp)
  apply (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)
  apply (case_tac x; wpsimp)
  done

lemma arch_invoke_irq_control_ctE_E[wp]:
  "arch_invoke_irq_control x2
   \<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: hoare_vcg_conj_lift)
     apply (rule valid_validE)
     apply (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)
    apply (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)
   apply wpsimp
  by simp

lemma invoke_irq_control_ct_on_exception:
  "\<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_chargeable\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. ct_not_queued and ct_not_in_release_q and cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  by (case_tac x; wpsimp)

lemma perform_invocation_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   perform_invocation a b c iv
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
  apply (wpsimp wp: invoke_irq_control_scheduler_act_sane invoke_cnode_scheduler_act_sane)+
  done

lemma invs_strengthen_cur_sc_tcb_only_sym_bound:
  "cur_sc_tcb_are_bound s \<and> invs s \<Longrightarrow> cur_sc_tcb_only_sym_bound s"
  unfolding cur_sc_tcb_only_sym_bound_def cur_sc_tcb_are_bound_def
  apply clarsimp
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma perform_invocation_ct_on_exception:
  "\<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_tcb_are_bound and
    scheduler_act_sane and valid_ntfn_q and valid_ep_q and ct_not_blocked and invs and
    valid_invocation iv\<rbrace>
   perform_invocation a b c iv
   -, \<lbrace>\<lambda>rv. ct_not_queued and ct_not_in_release_q and cur_sc_chargeable :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
             apply wpsimp
              apply (strengthen strengthen_cur_sc_chargeable, wpsimp)
             apply (fastforce intro: invs_strengthen_cur_sc_tcb_only_sym_bound)
            apply (wpsimp)+
         apply (wpsimp wp: hoare_vcg_E_conj hoare_elim_pred_conjE2 invoke_tcb_cur_sc_chargeable)
         apply (fastforce intro: invs_strengthen_cur_sc_chargeable)
        apply (wpsimp wp: invoke_cnode_scheduler_act_sane_new)+
     apply (fastforce intro: invs_strengthen_cur_sc_chargeable)
    apply (wpsimp wp:  invoke_irq_control_ct_on_exception)+
    apply (fastforce intro: invs_strengthen_cur_sc_chargeable)
   apply (wpsimp wp:  )+
  apply (wpsimp wp: hoare_vcg_E_conj hoare_elim_pred_conjE2)
     apply (wpsimp wp: ct_not_queued_lift)
    apply (wpsimp wp: ct_not_in_release_q_lift)
   apply (strengthen strengthen_cur_sc_chargeable)
   apply wpsimp
  apply (fastforce intro: invs_strengthen_cur_sc_tcb_only_sym_bound)
  done

lemma handle_invocation_schact_saneE_E:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q\<rbrace>
   handle_invocation a b c d x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
     by (wpsimp wp: perform_invocation_scheduler_act_sane hoare_drop_imps ct_in_state_set
                    set_thread_state_ct_valid_ep_q set_thread_state_ct_valid_ntfn_q)

lemma update_time_stamp_cur_sc_tcb_are_bound[wp]:
  "update_time_stamp \<lbrace>cur_sc_tcb_are_bound\<rbrace>"
  unfolding cur_sc_tcb_are_bound_def
  by (rule hoare_weaken_pre, wps, wpsimp, simp)

lemma handle_invocationE_E:
  "\<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_tcb_are_bound and
              scheduler_act_sane and
              valid_ntfn_q and
              valid_ep_q and invs and ct_active\<rbrace>
   handle_invocation a b c d x
   -, \<lbrace>\<lambda>rv. ct_not_queued and ct_not_in_release_q and cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wpsimp wp: syscall_valid perform_invocation_ct_on_exception[simplified pred_conj_def conj_assoc]
                    set_thread_state_ct_in_state hoare_drop_imps set_thread_state_ct_valid_ntfn_q
                    set_thread_state_ct_valid_ep_q)
      apply (rule validE_cases_valid, clarsimp)
      apply (subst validE_R_def[symmetric])
      apply (rule_tac Q'="\<lambda>r s.
             ct_not_queued s \<and>
             ct_not_in_release_q s \<and>
             cur_sc_tcb_are_bound s \<and>
             scheduler_act_sane s \<and>
             valid_ntfn_q s \<and>
             thread = cur_thread s \<and>
             valid_ep_q s \<and>
             ct_active s \<and>
             invs s \<and> valid_invocation r s" in hoare_post_imp_R[rotated])
       apply (clarsimp)
       apply (intro conjI)
          apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
         apply (clarsimp simp: ct_in_state_def)
        apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
        apply (erule if_live_then_nonz_cap_invs, assumption)
        apply (fastforce simp: live_def split: thread_state.split)
       apply (rule fault_tcbs_valid_states_active, clarsimp)
       apply (simp add: ct_in_state_def)
      apply (wp decode_inv_wf)
     apply wpsimp
     apply (rule validE_cases_valid, clarsimp)
     apply (subst validE_R_def[symmetric])
     apply wpsimp+
  done

crunches create_cap, cap_insert
  for scheduler_act_sane[wp]: "scheduler_act_sane:: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps )

lemma make_arch_fault_msg_scheduler_act_sane[wp]:
  "make_arch_fault_msg a b \<lbrace>scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp | wps)+

lemma reply_push_scheduler_act_sane[wp]:
  "reply_push caller callee reply_ptr can_donate \<lbrace>scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift | safe)+

crunches do_ipc_transfer
  for scheduler_act_sane[wp]: "scheduler_act_sane:: det_state \<Rightarrow> _"
  (wp: crunch_wps)

crunches update_time_stamp
  for scheduler_act_sane[wp]: "scheduler_act_sane:: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps)

lemma check_budget_restart_gen:
  "\<lbrace>P\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>r s. r \<longrightarrow> P (s:: det_state)\<rbrace>"
  unfolding check_budget_restart_def check_budget_def
  apply (wpsimp wp: hoare_vcg_if_lift2 gts_wp)
  apply (wpsimp wp: hoare_drop_imp)+
  done

lemma handle_event_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and valid_ep_q and valid_ntfn_q and valid_machine_time\<rbrace>
   handle_event e
   -, \<lbrace>\<lambda>rv. scheduler_act_sane:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       apply (rename_tac syscall)
       apply (case_tac syscall; simp)
                 apply ((wpsimp simp: handle_send_def handle_call_def imp_conjR
                                  wp: handle_invocation_schact_saneE_E
                                      check_budget_restart_gen)+)[11]
      apply wpsimp+
  done

lemma handle_event_ct_conditionsE_E:
  "\<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_tcb_are_bound
    and ct_active and invs and scheduler_act_sane and valid_ep_q and valid_ntfn_q and valid_machine_time\<rbrace>
   handle_event e
   -, \<lbrace>\<lambda>rv. ct_not_queued
            and ct_not_in_release_q
            and cur_sc_chargeable:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       apply (rename_tac syscall)
       apply (case_tac syscall; simp)
                 apply (wpsimp simp: handle_send_def handle_call_def
                                 wp: handle_invocationE_E check_budget_restart_gen)+
  done

lemma valid_ep_q_ct_not_in_ep_q:
  "valid_ep_q s \<Longrightarrow> t = cur_thread s \<Longrightarrow> \<not> in_ep_q t s"
  unfolding valid_ep_q_def
  by (fastforce simp: in_ep_q_def obj_at_def simple_obj_at_def split: option.splits)

lemma misc_cur_sc_tcb_bound[wp]:
  "update_sched_context csc_ptr f \<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s\<rbrace>"
  "set_refills a b \<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s\<rbrace>"
  "refill_budget_check t1 \<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s\<rbrace>"
  apply (rule hoare_lift_Pf[where f=cur_thread])
  apply (rule hoare_lift_Pf[where f=cur_sc])
  apply wpsimp+
  apply (rule hoare_lift_Pf[where f=cur_thread])
  apply (rule hoare_lift_Pf[where f=cur_sc])
  apply wpsimp+
  apply (rule hoare_lift_Pf[where f=cur_sc])
  apply (wpsimp wp: refill_budget_check_bound_sc)+ (* fixme: cleanup *)
  done

lemma round_robin_refills_sum:
  "length (sc_refills sc) = MIN_REFILLS \<Longrightarrow>
   r_amount (refill_hd sc) + r_amount (refill_tl sc) = refills_sum (sc_refills sc)"
  apply (clarsimp simp: MIN_REFILLS_def)
  apply (case_tac "sc_refills sc"; simp)
  apply (case_tac "list"; simp)
  done
(*
lemma charge_budget_valid_sched_helper:
  " \<lbrace>\<lambda>s. (valid_sched and invs and ct_not_in_release_q and ct_not_queued and
              schact_is_rct and
              valid_ep_q and
              ct_schedulable and
              (\<lambda>s. cur_sc s = csc_ptr))
              s \<and>
             (\<exists> sc n. ko_at (SchedContext sc n) (cur_sc s) s)\<rbrace>
       do ct <- gets cur_thread;
          st <- get_thread_state ct;
          when (runnable st) (do sc_opt <- get_tcb_obj_ref tcb_sched_context ct;
                                 y <- assert (sc_opt = Some csc_ptr);
                                 y <- end_timeslice canTimeout;
                                 y <- reschedule_required;
                                 modify (reprogram_timer_update (\<lambda>_. True))
                              od)
       od
       \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac "runnable st"; clarsimp)
   apply (wpsimp wp: reschedule_required_valid_sched )
*) (* used in charge_budget_valid_sched *)

(* shouldn't schact_is_rct be an abbreviation? *)
lemma schact_is_rct_consumed_time_update[simp]:
  "schact_is_rct (s\<lparr>consumed_time := new\<rparr>) = schact_is_rct s"
  by (clarsimp simp: schact_is_rct_def)

lemma update_sched_context_schact_is_rct[wp]:
  "\<lbrace>schact_is_rct\<rbrace> update_sched_context scp f  \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
     (clarsimp simp: schact_is_rct_def)

lemma set_refills_schact_is_rct[wp]:
  "\<lbrace>schact_is_rct\<rbrace> set_refills scp f  \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  by (wpsimp simp: set_refills_def update_sched_context_def set_object_def wp: get_object_wp)
     (clarsimp simp: schact_is_rct_def)

lemma refill_budget_check_schact_is_rct[wp]:
  "\<lbrace>schact_is_rct\<rbrace> refill_budget_check scp  \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  by (wpsimp simp: refill_budget_check_def Let_def
               wp: is_round_robin_wp refill_ready_wp refill_full_wp)

lemma update_sc_consumed_budget_sufficient'[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>
   update_sched_context csc (sc_consumed_update f)
   \<lbrace>\<lambda>_ s:: det_state. P (budget_sufficient t s) \<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  by (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def
               cong: conj_cong imp_cong split: option.splits) fastforce

lemma update_sc_consumed_budget_ready'[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>
   update_sched_context csc (sc_consumed_update f)
   \<lbrace>\<lambda>_ s:: det_state. P (budget_ready t s) \<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def
                  cong: conj_cong imp_cong split: option.splits)
  apply fastforce
  done

(*
lemma refill_budget_check_budget_sufficient:
  "\<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s \<and> valid_refills (cur_sc s) budget s\<rbrace>
   refill_budget_check usage capacity
   \<lbrace>\<lambda>_ s:: det_state. budget_sufficient (cur_thread s) s \<rbrace>"
  unfolding refill_budget_check_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp split del: if_split)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (case_tac "capacity=0"; clarsimp)
  *) (* currently not used? *)

(*
lemma refill_budget_check_budget_ready:
  "\<lbrace>\<lambda>s. budget_ready (cur_thread s) s\<rbrace>
   refill_budget_check usage capacity
   \<lbrace>\<lambda>_ s:: det_state. budget_ready (cur_thread s) s \<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: update_sched_context_wp simp: refill_full_def)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def
                  cong: conj_cong imp_cong split: option.splits)
  apply fastf orce
  *) (* currently not used? *)

lemma update_sched_context_weak_valid_sched_action':
  "\<lbrace>weak_valid_sched_action
    and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))
    and K (\<forall>sc. sc_refills (f sc) = sc_refills (sc))
    and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
      update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (intro conjI)
     apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
    apply (fastforce simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev refill_sufficient_kh_def is_refill_sufficient_def)
   apply (fastforce simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev refill_ready_kh_def is_refill_ready_def)
  apply (fastforce simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev refill_ready_kh_def is_refill_ready_def)
  done

lemma update_sched_context_valid_blocked':
  "\<lbrace>valid_blocked and K (\<forall>sc. sc_refill_max sc > 0 \<longleftrightarrow> sc_refill_max (f sc) > 0)\<rbrace>
     update_sched_context ptr f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_blocked_def)
  apply (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)
  done

crunches set_refills
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P t s)"

crunches set_refills, refill_budget_check
  for scheduler_act_sane[wp]: scheduler_act_sane
  (simp: crunch_simps)

lemma valid_ep_q_has_budget:
  "valid_ep_q s \<Longrightarrow> in_ep_q t s \<Longrightarrow> has_budget t s"
  by (fastforce simp: valid_ep_q_def in_ep_q_def obj_at_def simple_obj_at_def has_budget_def2 split: option.splits)

lemma valid_ep_q_in_ep_qD:
  "valid_ep_q s
   \<Longrightarrow> in_ep_q t s
   \<Longrightarrow> (st_tcb_at (\<lambda>ts. (\<exists>eptr r_opt. ts = BlockedOnReceive eptr r_opt) \<or>
                        (\<exists>eptr pl. ts = BlockedOnSend eptr pl)) t s
        \<and> t \<noteq> cur_thread s
        \<and> t \<noteq> idle_thread s
        \<and> has_budget t s)"
  apply (clarsimp simp: valid_ep_q_def2 in_ep_q_def simple_obj_at_def split: option.splits)
  apply (drule_tac x=ptr and y=t in spec2 )
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: has_budget_def2)
  done

lemma valid_ready_qs_has_budget:
  "valid_ready_qs s \<Longrightarrow> in_ready_q t s \<Longrightarrow> has_budget t s"
  by (clarsimp simp: valid_ready_qs_def in_ready_q_def obj_at_def has_budget_def2 split: option.splits)

lemma sc_with_tcb_propE1:
  "P t s
   \<Longrightarrow> (\<forall>tp. bound_sc_tcb_at ((=) (Some scp)) tp s \<longrightarrow> tp = t)
   \<Longrightarrow> sc_with_tcb_prop scp P s"
  by clarsimp

lemma valid_refills_round_robin_refills_sum:
  "valid_refills scp k s \<Longrightarrow>
   kheap s scp = Some (SchedContext sc n) \<Longrightarrow>
   sc_period sc = 0 \<Longrightarrow>
   (r_amount (refill_hd sc) + r_amount (refill_tl sc) = k)"
  unfolding valid_refills_def
  apply (clarsimp simp: obj_at_def MIN_REFILLS_def)
  apply (case_tac "sc_refills sc"; simp)
  apply (intro conjI; intro allI impI)
  apply (clarsimp)
  apply (case_tac "list"; simp)
  done

crunches refill_budget_check
  for bound_sc_tcb_at[wp]: "\<lambda>s. Q (bound_sc_tcb_at P t s)"
  and sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P t s)"

lemma charge_budget_valid_sched:
  "\<lbrace>valid_sched and invs and ct_not_in_release_q and ct_not_queued and scheduler_act_sane and valid_ep_q
    and cur_sc_chargeable and (\<lambda>s. valid_refills (cur_sc s) (-1) s)\<rbrace>
   charge_budget capacity consumed canTimeout
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply (wpsimp wp: reschedule_required_valid_sched' assert_inv
                    end_timeslice_valid_sched_subset )
         apply (wpsimp wp: gts_wp is_schedulable_wp)+
      apply (rule_tac Q="\<lambda>ya s.
               (if (st_tcb_at runnable (cur_thread s) s \<and> ct_not_in_release_q s \<and> active_sc_tcb_at (cur_thread s) s)
                then valid_release_q s \<and>
                     ct_not_queued s \<and> invs s \<and> valid_ep_q s \<and>
                     scheduler_act_sane s \<and> cur_sc_chargeable s \<and>
                     valid_ready_qs s \<and>
                     weak_valid_sched_action s \<and> valid_blocked s \<and> valid_idle_etcb s
                else valid_sched s)" in hoare_strengthen_post[rotated])
       apply clarsimp
       apply (case_tac t; clarsimp)
       apply (clarsimp split: if_splits option.splits
                        simp: valid_sched_def valid_sched_action_def pred_tcb_at_def obj_at_def
                              ct_in_state_def is_schedulable_opt_def cur_sc_chargeable_def
                       dest!: get_tcb_SomeD)
       apply (case_tac "tcb_state x2"; simp)
       apply (clarsimp simp: in_release_queue_def not_in_release_q_def)
       apply (clarsimp simp: active_sc_tcb_at_defs)
       apply (clarsimp split: if_splits option.splits
                        simp: valid_sched_def valid_sched_action_def pred_tcb_at_def obj_at_def
                              ct_in_state_def is_schedulable_opt_def schact_is_rct_def cur_tcb_def
                              is_tcb active_sc_tcb_at_defs
                       dest!: get_tcb_SomeD)
       apply (clarsimp simp: in_release_queue_def not_in_release_q_def)
     apply (wpsimp wp: hoare_vcg_if_lift_strong)
         apply wps
         apply (wpsimp wp: active_sc_tcb_at_update_sched_context_no_change)
        apply (rule hoare_weaken_pre)
         apply wps
         apply (wpsimp wp: hoare_vcg_imp_lift active_sc_tcb_at_update_sched_context_no_change)
        apply simp
       apply (wpsimp wp: sc_consumed_update_valid_queues ct_not_in_release_q_lift cur_sc_chargeable_lift
                         update_sched_context_weak_valid_sched_action' active_sc_tcb_at_cur_thread_lift
                         update_sched_context_valid_blocked' update_sched_context_cur_sc_tcb_no_change
                         update_sched_context_sc_tcb_sc_at
                         active_sc_tcb_at_update_sched_context_no_change sc_consumed_add_invs)
      apply (wp update_sc_consumed_valid_sched)
     apply (clarsimp simp: )
     apply (wpsimp simp: Let_def)
       apply (wpsimp wp: hoare_vcg_if_lift_strong)
          apply wps
          apply wpsimp
         apply (rule hoare_weaken_pre)
          apply wps
          apply (wpsimp, simp)
        apply (wpsimp wp: set_refills_valid_release_q set_refills_valid_ready_qs
                          set_refills_valid_ep_q cur_sc_chargeable_lift
                          ct_not_in_release_q_lift ct_not_queued_lift
                          active_sc_tcb_at_cur_thread_lift
                          set_refills_valid_blocked_except_set set_refills_weak_valid_sched_action_act_not)
       apply (wpsimp simp: valid_sched_def
                       wp: set_refills_valid_release_q set_refills_valid_ready_qs
                           set_refills_valid_blocked_except_set set_refills_valid_sched_action_act_not)
      apply (wpsimp wp: get_refills_wp)
     apply (wpsimp wp: hoare_vcg_if_lift_strong)
        apply wps
        apply (wpsimp wp: refill_budget_check_st_tcb_at)
       apply (rule hoare_weaken_pre)
        apply wps
        apply (wpsimp wp: refill_budget_check_st_tcb_at hoare_vcg_imp_lift')
       apply (clarsimp simp: not_in_release_q_def in_release_queue_def)
      apply (wpsimp wp: refill_budget_check_valid_ready_qs refill_budget_check_valid_release_q
                        refill_budget_check_weak_valid_sched_action_act_not
                        refill_budget_check_valid_ep_q cur_sc_chargeable_lift
                        refill_budget_check_valid_blocked refill_budget_check_valid_idle_etcb
                        ct_not_in_release_q_lift ct_not_queued_lift
                        active_sc_tcb_at_cur_thread_lift refill_budget_check_invs)
     apply (wpsimp wp: refill_budget_check_valid_sched)
    apply (wpsimp simp: is_round_robin_def)+
  apply (clarsimp simp: valid_sched_def valid_sched_action_def split: if_splits)
  apply (intro conjI; intro impI allI)
   apply (subgoal_tac "bound_sc_tcb_at (\<lambda>x. x = (Some (cur_sc s))) (cur_thread s) s")
    apply (intro conjI; intro impI allI)
     apply (intro conjI; intro impI allI)
        apply (clarsimp simp: obj_at_def)
       apply (intro conjI)
        apply (rule_tac s=s and scp="cur_sc s" in budgets_bounded_below)
        apply (clarsimp simp: obj_at_def)
        apply (frule_tac sc = sc in valid_refills_round_robin_refills_sum, assumption, assumption, clarsimp)
       apply (frule valid_ep_q_has_budget, assumption)
       apply (clarsimp simp: has_budget_def2 active_sc_tcb_at_defs is_refill_ready_def is_refill_sufficient_def)
      apply (intro conjI)
       apply (rule_tac s=s and scp="cur_sc s" in budgets_bounded_below)
       apply (clarsimp simp: obj_at_def)
       apply (frule_tac sc = sc in valid_refills_round_robin_refills_sum, assumption, assumption, clarsimp)
      apply (frule valid_ready_qs_has_budget, assumption)
      apply (clarsimp simp: has_budget_def2 active_sc_tcb_at_defs is_refill_ready_def is_refill_sufficient_def)
     apply (subgoal_tac "tp = cur_thread s")
      apply (clarsimp simp: scheduler_act_sane_def)
     apply (clarsimp simp: pred_tcb_at_eq_commute)
     apply (erule sym_refs_bound_sc_tcb_at_inj[rotated]; clarsimp)
    apply (intro conjI)
      apply (erule sc_with_tcb_propE1; clarsimp)
      apply (clarsimp simp: pred_tcb_at_eq_commute)
      apply (erule sym_refs_bound_sc_tcb_at_inj[rotated]; clarsimp)
     apply (intro allI impI)
     apply (subgoal_tac "tp = cur_thread s", clarsimp)
      apply (drule valid_ep_q_in_ep_qD, assumption)
      apply (clarsimp simp: obj_at_def pred_tcb_at_def)
     apply (clarsimp simp: pred_tcb_at_eq_commute)
     apply (erule sym_refs_bound_sc_tcb_at_inj[rotated]; clarsimp)
    apply (erule sc_with_tcb_propE1; clarsimp)
    apply (clarsimp simp: pred_tcb_at_eq_commute)
    apply (erule sym_refs_bound_sc_tcb_at_inj[rotated]; clarsimp)
   apply (clarsimp simp: active_sc_tcb_at_defs cur_sc_chargeable_def)
  apply (intro conjI; intro impI allI)
   apply (intro conjI; intro impI allI)
    apply (clarsimp simp: obj_at_def)
   apply (intro conjI; intro impI allI)
     apply (intro conjI)
      apply (rule_tac s=s and scp="cur_sc s" in budgets_bounded_below)
      apply (clarsimp simp: obj_at_def)
      apply (frule_tac sc = sc in valid_refills_round_robin_refills_sum, assumption, assumption, clarsimp)
     apply (frule valid_ready_qs_has_budget, assumption)
     apply (clarsimp simp: has_budget_def2 active_sc_tcb_at_defs is_refill_ready_def is_refill_sufficient_def)
    apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: pred_tcb_at_eq_commute)
   apply (frule cur_sc_chargeableD, simp, erule disjE)
    apply (clarsimp simp: scheduler_act_sane_def)
   apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def pred_tcb_at_def obj_at_def)
  apply (intro conjI)
(*
    apply (clarsimp simp: pred_tcb_at_eq_commute)
    apply (frule cur_sc_chargeableD, simp, erule disjE)
     apply clarsimp
    apply (erule valid_ready_qs_not_runnable_not_inq)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: pred_tcb_at_eq_commute)
   apply (frule cur_sc_chargeableD, simp, erule disjE)
    apply clarsimp
   apply (erule valid_release_q_not_runnable_not_inq)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: pred_tcb_at_eq_commute)
  apply (frule cur_sc_chargeableD, simp, erule disjE)
   apply clarsimp
  apply (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def pred_tcb_at_def obj_at_def)
*)
    apply (erule sc_with_tcb_propE1; clarsimp simp: pred_tcb_at_eq_commute)
    apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
    apply (clarsimp simp: cur_sc_cur_thread_bound_def)
   apply (erule sc_with_tcb_propE1; clarsimp simp: pred_tcb_at_eq_commute)
   apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
   apply (clarsimp simp: cur_sc_cur_thread_bound_def)
  apply (erule sc_with_tcb_propE1; clarsimp simp: pred_tcb_at_eq_commute)
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
(*    apply (subgoal_tac "
          (\<forall>t. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) t s \<longrightarrow> not_queued t s \<and> \<not> in_ep_q t s)")
     apply clarsimp
     apply (subgoal_tac "budget_sufficient tcb_ptr s \<and> budget_ready tcb_ptr s")
      apply (clarsimp simp: obj_at_def pred_tcb_at_def is_refill_ready_def is_refill_sufficient_def
                             sufficient_refills_def refills_capacity_def)
  subgoal sorry \<comment> \<open>check r_times\<close>
     apply (clarsimp simp: obj_at_def)
     apply (clarsimp simp: valid_ready_qs_def in_ready_q_def)
    apply (clarsimp simp: schact_is_rct_def)
    apply (subgoal_tac "t = cur_thread s")
     apply (clarsimp elim!: valid_ep_q_ct_not_in_ep_q)
    apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. x = Some (cur_thread s)) (cur_sc s) s")
     apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. x = Some (t)) (cur_sc s) s")
      apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
     apply ((subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric, OF refl refl]); clarsimp)
    apply ((subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric, OF refl refl]); clarsimp)
   apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def cur_sc_cur_thread_bound_def)
  apply (intro conjI; intro allI impI)
    apply (intro conjI; intro allI impI)
     apply (intro conjI allI impI)
  subgoal sorry \<comment> \<open>easy\<close>
  subgoal sorry \<comment> \<open>check r_times\<close>
  subgoal sorry \<comment> \<open>easy\<close>
  subgoal sorry \<comment> \<open>check r_times\<close>
     apply clarsimp
    apply (intro conjI)
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply (intro conjI)
  subgoal sorry \<comment> \<open>easy\<close>
  subgoal sorry \<comment> \<open>check r_times\<close>
  apply ((subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl]), clarsimp)
  apply (subgoal_tac "t = cur_thread s")
   apply clarsimp
*)
  apply (clarsimp simp: cur_sc_cur_thread_bound_def)
  done

lemma check_budget_valid_sched:
  "\<lbrace>valid_sched and invs and ct_not_in_release_q and ct_not_queued
    and (\<lambda>s. valid_refills (cur_sc s) s)
    and scheduler_act_sane and cur_sc_chargeable\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (wpsimp wp: get_sched_context_wp charge_budget_valid_sched
                    reschedule_valid_sched_const
                    hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)
  apply (erule valid_sched_implies_valid_ipc_qs)
  done

lemma tcb_sched_dequeue_valid_blocked_except_set:
  "\<lbrace>\<lambda>s. if not_queued tcb_ptr s then valid_blocked_except_set {tcb_ptr} s else valid_blocked s\<rbrace>
   tcb_sched_action tcb_sched_dequeue tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except_set {tcb_ptr} s\<rbrace>"
  unfolding tcb_sched_action_def
  apply (wpsimp)
  apply (clarsimp simp: valid_blocked_except_set_def tcb_sched_dequeue_def obj_at_def split: if_splits)
   apply (drule_tac x=t in spec; clarsimp )
   apply (case_tac "not_queued t s"; clarsimp)
   apply (clarsimp simp: not_queued_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply (drule_tac x=p in spec)
   apply (fastforce simp: tcb_sched_dequeue_def split: if_splits)
  apply (clarsimp simp: not_queued_def valid_blocked_def)
  apply (drule_tac x=t in spec; clarsimp )
  apply (auto simp: tcb_sched_dequeue_def split: if_splits)
  done

lemma tcb_release_remove_valid_blocked_except_set:
  "\<lbrace>\<lambda>s. if not_in_release_q tcb_ptr s then valid_blocked_except tcb_ptr s else valid_blocked s\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except tcb_ptr s\<rbrace>"
  unfolding tcb_release_remove_def
  apply (wpsimp)
  apply (clarsimp simp: valid_blocked_except_set_def tcb_sched_dequeue_def obj_at_def split: if_splits)
   apply (drule_tac x=t in spec; clarsimp )
   apply (case_tac "not_in_release_q t s"; clarsimp)
   apply (clarsimp simp: not_in_release_q_def in_release_queue_def not_in_release_q_2_def)
  apply (clarsimp simp: not_in_release_q_2_def in_queue_2_def)
  apply (drule_tac x=t in spec; clarsimp simp: not_in_release_q_def)
  done

lemma tcb_release_remove_sc_tcb_at[wp]:
  "\<lbrace>sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv. sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr\<rbrace>"
   unfolding tcb_release_remove_def
   by wpsimp

lemma tcb_queue_remove_schact_is_rct:
  "tcb_sched_action tcb_sched_dequeue tcb_ptr \<lbrace>schact_is_rct\<rbrace>"
  "tcb_release_remove tcb_ptr \<lbrace>schact_is_rct\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def tcb_release_remove_def schact_is_rct_def)+

lemma tcb_release_remove_budgetRandS[wp]:
  "tcb_release_remove t \<lbrace>\<lambda>s. budget_ready t' s\<rbrace>"
  "tcb_release_remove t \<lbrace>\<lambda>s. budget_sufficient t' s\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def is_refill_ready_def is_refill_sufficient_def)+

lemma update_sched_context_tcb_ready_time:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s) \<and> (\<forall>x. sc_refills (f x) = sc_refills x)\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def
                wp: get_object_wp split_del: if_split)
  apply (clarsimp simp: obj_at_def tcb_ready_time_def elim!: rsubst[where P=P])
  by (clarsimp simp: active_sc_tcb_at_defs get_tcb_def hd_append
              split: option.splits dest!: get_tcb_SomeD)

lemma update_sched_context_valid_sched_no_change:
  "\<forall>x. (0 < sc_refill_max (f x)) = (0 < sc_refill_max x) \<Longrightarrow>
   \<forall>x. sc_refills (f x) = sc_refills x \<Longrightarrow>
   \<lbrace>valid_sched\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
   by (wpsimp wp: valid_sched_lift active_sc_tcb_at_update_sched_context_no_change
                  update_sched_context_tcb_ready_time
                  budget_ready_update_sched_context_no_change
                  budget_sufficient_update_sched_context_no_change)

(* FIXME: schact_is_rct should be simpler to allow this to be crunched *)
lemma update_sched_context_schat_is_rct[wp]:
  "update_sched_context sc_ptr f \<lbrace>\<lambda>s. schact_is_rct s\<rbrace>"
  by (wpsimp simp: schact_is_rct_def)

(* FIXME: ready_or_released should be structured to make this trivial *)
lemma update_sched_context_ready_or_released[wp]:
  "update_sched_context sc_ptr f \<lbrace>\<lambda>s. ready_or_released s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: ready_or_released_def)
  done

lemma tcb_sched_action_valid_refills_cur_sc[wp]:
  "tcb_sched_action f tcb_ptr \<lbrace>\<lambda>s. valid_refills (cur_sc s) s\<rbrace>"
  apply (rule hoare_weaken_pre)
  by (wpsimp | wps)+

lemma tcb_release_remove_valid_refills_cur_sc[wp]:
  "tcb_release_remove tcb_ptr \<lbrace>\<lambda>s. valid_refills (cur_sc s) s\<rbrace>"
  apply (rule hoare_weaken_pre)
  by (wpsimp | wps)+

lemma update_sched_context_valid_refills_indep:
  "\<forall>sc. sc_refills (f sc) = sc_refills sc \<Longrightarrow>
   \<forall>sc. sc_refill_max (f sc) = sc_refill_max sc \<Longrightarrow>
   \<forall>sc. sc_period (f sc) = sc_period sc \<Longrightarrow>
   \<forall>sc. sc_budget (f sc) = sc_budget sc \<Longrightarrow>
   update_sched_context sc_ptr f \<lbrace>valid_refills t\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  done

lemma sc_badge_update_valid_refills_cur_sc[wp]:
  "update_sched_context sc_ptr (sc_badge_update j) \<lbrace>\<lambda>s. valid_refills (cur_sc s) s\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (wps | wpsimp wp: update_sched_context_valid_refills_indep)+
  done

crunches commit_time, reschedule_required, postpone
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunches send_ipc
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunches check_budget
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunches tcb_sched_action, tcb_release_remove, update_sched_context
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"

lemma pst_vs_for_invoke_sched_control_configure:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and st_tcb_at runnable target
    and (\<lambda>s. target \<noteq> idle_thread s)
    and (\<lambda>s. not_in_release_q target s \<longrightarrow> has_budget target s)\<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wp possible_switch_to_valid_sched_strong)
  apply (clarsimp simp: valid_sched_def )
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp:  has_budget_def)
  apply (erule valid_blocked_divided2, clarsimp)
  apply (clarsimp simp: in_release_queue_def not_in_release_q_def active_sc_tcb_at_defs)
  done


(* when check_budget returns True, it has not called charge_budget. Hence the
ct_not_in_release_q remains true *)
lemma check_budget_true_ct_not_in_release_q:
  "\<lbrace> \<lambda>s. ct_not_in_release_q s \<rbrace>
     check_budget
   \<lbrace> \<lambda>rv s. rv \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ refill_capacity_sp])
  apply (rule hoare_if)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_if)
    by wpsimp+

lemma invoke_sched_control_configure_valid_sched:
  "\<lbrace>valid_sched and valid_sched_control_inv iv and schact_is_rct and ready_or_released and invs and valid_machine_time
    and ct_not_in_release_q and ct_ARS and ct_not_queued and (\<lambda>s. valid_refills (cur_sc s) s)\<rbrace>
     invoke_sched_control_configure iv
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding invoke_sched_control_configure_def
  supply if_split [split del]
  apply (cases iv; simp)
  apply (rename_tac sc_ptr budget period mrefills badge)
  apply (clarsimp simp: liftE_def bind_assoc)
  apply (wp|wpc)+
                apply (wpsimp wp: reschedule_valid_sched_const)
               apply (wpsimp wp: possible_switch_to_valid_sched_weak)
              apply wpsimp
             apply (rule hoare_vcg_conj_lift)
              apply (wpsimp wp: hoare_drop_imp sched_context_resume_valid_sched)
             apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift)
              apply (wpsimp wp: sched_context_resume_valid_ready_qs
                                sched_context_resume_valid_release_q
                                sched_context_resume_valid_sched_action
                                sched_context_resume_ct_in_cur_domain
                                sched_context_resume_valid_blocked_except_set
                                hoare_drop_imp sched_context_resume_budget_ready
                                sched_context_resume_budget_sufficient
                          simp: has_budget_equiv)
             apply (wpsimp wp: hoare_drop_imp sched_context_resume_valid_sched)
            apply (wpsimp wp: get_sched_context_wp)
           apply wpsimp
(*
  apply (wpsimp wp: reschedule_valid_sched_const)
               apply (wpsimp wp: pst_vs_for_invoke_sched_control_configure)
              apply wpsimp
             apply (wpsimp wp: hoare_vcg_imp_lift' sched_context_resume_valid_sched hoare_vcg_if_lift_strong)
              apply (wpsimp wp: hoare_vcg_if_lift_strong sched_context_resume_valid_ready_qs sched_context_resume_valid_release_q2
              apply (wpsimp wp: hoare_vcg_if_lift_strong sched_context_resume_valid_ready_qs sched_context_resume_valid_release_q
                                sched_context_resume_valid_sched_action sched_context_resume_ct_in_cur_domain
                                sched_context_resume_valid_blocked_except_set sched_context_resume_not_in_release_q )
             apply (wpsimp wp: hoare_vcg_imp_lift'
                               sched_context_resume_valid_sched )
            apply (wpsimp | strengthen not_not_in_release_q_simp)+
           apply (clarsimp simp: valid_sched_def cong: conj_cong imp_cong if_cong)
           apply (rule_tac Q="\<lambda>yd s. sc_tcb_sc_at (\<lambda>t. t = Some tcb_ptr) sc_ptr s \<and>
                                     invs s \<and> simple_sched_action s \<and>
                                     valid_sched_except_blocked s \<and>
                                     test_sc_refill_max sc_ptr s \<and>
                                     st_tcb_at (\<lambda>x. x = st) tcb_ptr s \<and>
                                     valid_blocked_except_set {tcb_ptr} s"
                  in hoare_strengthen_post[rotated])
            apply (subgoal_tac "bound_sc_tcb_at (\<lambda>sc. sc = Some sc_ptr) tcb_ptr s")
             apply (subgoal_tac "st_tcb_at idle (idle_thread s) s")
              apply (clarsimp simp: sc_at_pred_n_def not_cur_thread_def valid_sched_def
                                    active_sc_tcb_at_defs
                             split: if_splits option.splits)
              apply (intro conjI impI allI; clarsimp simp: valid_blocked_except_set_cur_thread)
               apply (intro conjI impI exI allI, simp+)
              apply (erule valid_blocked_except_set_not_runnable; clarsimp simp: pred_tcb_at_def obj_at_def)
             apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def)
            apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl]; clarsimp)
           apply (rule hoare_vcg_if_split_strong)
            apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_if_lift_strong hoare_vcg_all_lift
                              refill_new_test_sc_refill_max refill_update_valid_ready_qs
                              refill_update_valid_release_q_not_in_release_q refill_update_valid_sched_action
                              refill_update_valid_blocked_except_set
                              refill_update_valid_blocked refill_update_invs refill_new_invs)
           apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_if_lift_strong hoare_vcg_all_lift
                             refill_new_test_sc_refill_max refill_new_valid_ready_qs
                             refill_new_valid_release_q refill_new_valid_sched_action refill_new_valid_blocked_except_set
                             )
          apply (wpsimp wp: gts_wp)
         apply (clarsimp simp: cong: conj_cong imp_cong if_cong all_cong)
         apply (rule_tac Q="\<lambda>yc s. sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr s \<and>
                                   sc_ptr \<noteq> idle_sc_ptr \<and> invs s \<and> valid_machine_time s \<and> not_in_release_q tcb_ptr s \<and>
                                   simple_sched_action s \<and> valid_sched_except_blocked s \<and>
                                   valid_blocked_except_set {tcb_ptr} s \<and>
                                   0 < mrefills \<and> MIN_BUDGET \<le> budget"
                in hoare_strengthen_post[rotated])
          apply (auto simp: cong: conj_cong imp_cong)[1]
            apply (clarsimp simp: MIN_REFILLS_def split: if_splits)
            apply (clarsimp simp: valid_release_q_def)
            apply (drule_tac x=t in bspec, simp, clarsimp simp: active_sc_tcb_at_defs split: option.splits)
            apply (clarsimp simp: obj_at_def not_in_release_q_def sc_tcb_sc_at_def)
            apply (drule invs_sym_refs)
            apply (drule_tac tp=t in ARM.sym_ref_tcb_sc, simp, simp)
            apply (clarsimp simp: state_refs_of_def get_refs_def2)
           apply (clarsimp simp: pred_tcb_at_def obj_at_def)
          apply (subgoal_tac "sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptra) sc_ptr s")
           apply (clarsimp simp: sc_at_pred_n_def obj_at_def split: if_splits)
          apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl, symmetric];
                 clarsimp split: if_splits)
         apply (rule hoare_when_wp)
         apply (rule_tac Q="\<lambda>yc s. sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr s \<and>
                                   sc_ptr \<noteq> idle_sc_ptr \<and> invs s \<and> valid_machine_time s \<and> ct_not_in_release_q s \<and>
                                   simple_sched_action s \<and> valid_sched s \<and>
                                   tcb_ptr = cur_thread s \<and> 0 < mrefills \<and> MIN_BUDGET \<le> budget"
                in hoare_strengthen_post[rotated])
          apply (clarsimp simp: valid_sched_def)
         apply (clarsimp split: if_splits)
         apply wpsimp
          apply (wpsimp wp: hoare_vcg_if_lift_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                            commit_time_valid_sched commit_time_invs)
         apply (rule_tac Q="\<lambda>x xa. sc_ptr \<noteq> idle_sc_ptr \<and>
                                   sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr xa \<and> invs xa \<and> valid_machine_time xa \<and>
                                   simple_sched_action xa \<and> valid_sched xa \<and>
                                   tcb_ptr = cur_thread xa \<and> 0 < mrefills \<and> MIN_BUDGET \<le> budget \<and>
                                   (x \<longrightarrow> schact_is_rct xa \<and> ct_not_queued xa \<and> ct_not_in_release_q xa)"
(*
                                   (x \<longrightarrow> ct_not_in_release_q xa) \<and>
                                   tcb_ptr = cur_thread xa \<and> 0 < mrefills \<and> MIN_BUDGET \<le> budget"
*)
                in hoare_strengthen_post[rotated])
          apply (clarsimp split: if_splits)
          apply (subgoal_tac "t = cur_thread s")
           apply clarsimp
          apply (subgoal_tac "sc_tcb_sc_at (\<lambda>a. a = Some t) (cur_sc s) s")
           apply (subgoal_tac "cur_sc_tcb s")
            apply (clarsimp simp: sc_at_pred_n_def obj_at_def cur_sc_tcb_def schact_is_rct_def)
           apply clarsimp
          apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl, symmetric]; clarsimp)
         apply (wpsimp wp: hoare_vcg_if_lift_strong
                           check_budget_valid_sched check_budget_true)
(*
          apply (clarsimp)
         apply (wpsimp wp: hoare_vcg_if_lift_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                           check_budget_valid_sched check_budget_true_ct_not_in_release_q)
*)
        apply wpsimp+
       apply (rule_tac Q="\<lambda>yb. invs and sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr and
                               schact_is_rct and valid_sched_except_blocked and
                               ct_not_in_release_q and ct_not_queued and ct_ARS and
                               (\<lambda>s. valid_refills (cur_sc s) (- 1) s) and valid_machine_time and
(*
                               schact_is_rct and valid_sched_except_blocked and not_in_release_q tcb_ptr and
*)
                               K (sc_ptr \<noteq> idle_sc_ptr) and valid_blocked_except_set {tcb_ptr} and
                               K (0 < mrefills \<and> MIN_BUDGET \<le> budget) "
             in hoare_strengthen_post[rotated])
        apply (clarsimp simp: valid_sched_def split: if_splits)
        apply (intro conjI; intro impI)
         apply (subgoal_tac "tcb_ptr = cur_thread s")
          apply (intro conjI; clarsimp)
            apply (erule schact_is_rct_simple)
           apply (clarsimp simp: valid_blocked_except_set_cur_thread)
          apply (fastforce elim: invs_cur_sc_chargeableE)
         apply (drule_tac t = sc_ptr in sym, clarsimp)
         apply (subgoal_tac "sc_tcb_sc_at (\<lambda>a. a = Some (cur_thread s)) (cur_sc s) s")
          apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
         apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric, OF refl refl invs_sym_refs], clarsimp)
         apply (fastforce elim: invs_cur_sc_tcb_symref)
        apply (erule schact_is_rct_simple)
       apply (wpsimp wp: hoare_vcg_if_lift_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                         tcb_sched_dequeue_valid_ready_qs tcb_sched_dequeue_valid_blocked_except_set
                         tcb_release_remove_valid_blocked_except_set tcb_dequeue_not_queued
                         tcb_queue_remove_schact_is_rct active_sc_tcb_at_cur_thread_lift ct_not_queued_lift
                         budget_ready_cur_thread_lift budget_sufficient_cur_thread_lift tcb_dequeue_not_queued_gen)
      apply (wpsimp wp: hoare_vcg_if_lift_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                        tcb_release_remove_sc_tcb_at tcb_sched_dequeue_valid_blocked_except_set
                        tcb_release_remove_valid_blocked_except_set tcb_release_remove_valid_blocked_not_queued
                        tcb_queue_remove_schact_is_rct active_sc_tcb_at_cur_thread_lift
                        budget_ready_cur_thread_lift budget_sufficient_cur_thread_lift)
     apply wpsimp
    apply clarsimp
    apply (rule_tac Q="\<lambda>_. valid_sched and
                           (if \<exists>y. sc_tcb sc = Some y
                            then \<lambda>s. invs s \<and> valid_refills (cur_sc s) s \<and> valid_machine_time s \<and>
                                     sc_tcb_sc_at (\<lambda>a. a = sc_tcb sc) sc_ptr s \<and>
                                     schact_is_rct s \<and> ready_or_released s \<and> ct_ARS s \<and>
                                     ct_not_in_release_q s \<and> ct_not_queued s \<and>
                                     sc_ptr \<noteq> idle_sc_ptr \<and> 0 < mrefills \<and> MIN_BUDGET \<le> budget
                            else \<top>)"
          in hoare_strengthen_post[rotated])
     apply (clarsimp simp: valid_sched_def ready_or_released_def not_queued_def not_in_release_q_def
                    split: if_splits;
            fastforce?)
    apply (wpsimp wp: hoare_vcg_if_lift_strong hoare_vcg_all_lift hoare_vcg_imp_lift'
                      update_sched_context_valid_sched_no_change update_sc_badge_invs'
                      active_sc_tcb_at_cur_thread_lift
                      budget_ready_cur_thread_lift budget_sufficient_cur_thread_lift
                      update_sched_context_sc_tcb_sc_at update_sched_context_scheduler_action
                      active_sc_tcb_at_update_sched_context_no_change
                      budget_ready_update_sched_context_no_change
                      budget_sufficient_update_sched_context_no_change ct_not_in_release_q_lift)
   apply wpsimp
  apply simp
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def split: if_splits)
  apply (intro allI impI conjI;
         clarsimp dest!: idle_sc_no_ex_cap simp: invs_def valid_state_def)
  apply (clarsimp simp: MIN_REFILLS_def)*)
  sorry (* waiting for the spec update*)

lemma perform_invocation_valid_sched:
  "\<lbrace>invs and valid_ntfn_q and valid_invocation i and ct_active and scheduler_act_sane and valid_sched
        and ready_or_released and valid_reply_scs and (\<lambda>s. valid_refills (cur_sc s) s) and valid_machine_time
        and (\<lambda>s. scheduler_action s = resume_cur_thread) and valid_ep_q and ct_not_queued and ct_not_in_release_q and ct_ARS\<rbrace>
     perform_invocation block call can_donate i
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases i; simp)
             apply (wpsimp wp: invoke_untyped_valid_sched)
            apply (wpsimp wp: send_ipc_valid_sched;
                   clarsimp simp: ct_in_state_def)
           apply (wpsimp wp: send_signal_valid_sched)
          apply (wpsimp wp: do_reply_transfer_valid_sched)
         apply (wpsimp wp: invoke_tcb_valid_sched;
                clarsimp simp: pred_tcb_at_def obj_at_def)
        apply (wpsimp wp: invoke_domain_valid_sched)
       apply (wpsimp wp: invoke_sched_context_valid_sched;
              clarsimp simp: pred_tcb_at_def obj_at_def)
      apply (wpsimp wp: invoke_sched_control_configure_valid_sched; (* this case may be wrong *)
             clarsimp simp: schact_is_rct_def)
     apply (wpsimp wp: invoke_cnode_valid_sched)
    apply (wpsimp wp: invoke_irq_control_valid_sched invoke_irq_handler_valid_sched;
           clarsimp simp: invs_valid_objs invs_valid_idle)
   apply (wpsimp wp: arch_perform_invocation_valid_sched;
          intro conjI; clarsimp)
  apply wpsimp
  done

end

context DetSchedSchedule_AI begin

definition
  ready_or_released2
where
  "ready_or_released2 ready_qs release_q \<equiv> \<forall>t d p. \<not> (t \<in> set (ready_qs d p) \<and> t \<in> set (release_q))"

abbreviation
  ready_or_released_better
where
  "ready_or_released_better s \<equiv> ready_or_released2 (ready_queues s) (release_queue s)"

lemmas ready_or_released_better_def = ready_or_released2_def

crunch ready_or_released_better[wp]: set_thread_state ready_or_released_better

lemma ready_or_released_better_equiv:
  "ready_or_released = ready_or_released_better"
  by (fastforce simp: ready_or_released_better_def ready_or_released_def)

lemma set_thread_state_ready_or_released[wp]:
  "\<lbrace>ready_or_released\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ready_or_released\<rbrace>"
  by (wpsimp simp: ready_or_released_better_equiv)

lemma set_thread_state_valid_reply_scs[wp]:
  "\<lbrace>valid_reply_scs\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_reply_scs ::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_reply_scs_lift set_thread_state_active_sc_tcb_at)

lemma is_schedulable_bool_def2:
  "is_schedulable_bool t a s = (st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> \<not> a)"
  apply (clarsimp simp: is_schedulable_bool_def get_tcb_def pred_tcb_at_def obj_at_def
                        active_sc_tcb_at_def
                 split: option.splits kernel_object.splits)
  done

lemma set_thread_state_valid_refills_cur_sc[wp]:
  "set_thread_state thread k \<lbrace>(\<lambda>s. valid_refills (cur_sc s) s)\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (wps | wpsimp)+
  done

lemma handle_invocation_valid_sched:
  "\<lbrace>invs and valid_sched and valid_ntfn_q and ready_or_released and ct_active and valid_ep_q and valid_machine_time
    and ct_not_queued and ct_not_in_release_q and valid_reply_scs  and (\<lambda>s. valid_refills (cur_sc s) s) and
    (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_ARS\<rbrace>
     handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid handle_fault_valid_sched | wpc)+
                apply (wp set_thread_state_runnable_valid_sched)[1]
               apply wp+
         apply (wp gts_wp hoare_vcg_all_lift)
        apply (rule_tac Q="\<lambda>_. valid_sched" and E="\<lambda>_. valid_sched" in hoare_post_impErr)
          apply (wp perform_invocation_valid_sched)
         apply ((clarsimp simp: st_tcb_at_def obj_at_def)+)[2]
       apply (wp ct_in_state_set set_thread_state_runnable_valid_sched
                 set_thread_state_ct_valid_ep_q set_thread_state_ct_valid_ntfn_q
                 sts_schedulable_scheduler_action
            hoare_vcg_E_conj | simp add: split_def if_apply_def2 split del: if_split)+
  apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_ready_qs_def not_queued_def
                    is_schedulable_bool_def2 ct_in_state_def runnable_eq_active not_in_release_q_def
                    in_release_queue_def)
  apply (auto elim: st_tcb_ex_cap intro: fault_tcbs_valid_states_active)
  done

end

lemma valid_sched_ct_not_queued:
  "\<lbrakk>valid_sched s; scheduler_action s = resume_cur_thread\<rbrakk> \<Longrightarrow>
    not_queued (cur_thread s) s"
  by (fastforce simp: valid_sched_def ct_not_in_q_def)

crunch ct_not_queued[wp]: do_machine_op, cap_insert, set_extra_badge
  "\<lambda>s::det_state. not_queued (cur_thread s) s"
  (wp: hoare_drop_imps)

lemma transfer_caps_ct_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
     transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

context DetSchedSchedule_AI begin

crunch sched_act_not[wp]: handle_fault_reply "scheduler_act_not t::det_state \<Rightarrow> _"

crunch cur[wp]: handle_fault_reply "cur_tcb :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

context DetSchedSchedule_AI begin
(*
crunch weak_valid_sched_action[wp]: blocked_cancel_ipc,cancel_signal weak_valid_sched_action

crunch weak_valid_sched_action[wp]: reply_remove_tcb weak_valid_sched_action
  (wp: hoare_drop_imps crunch_wps set_bound_notification_weak_valid_sched_action
   ignore: set_scheduler_action set_object)


crunch weak_valid_sched_action[wp]: set_mrs weak_valid_sched_action
  (simp: zipWithM_x_mapM wp: mapM_wp' ignore: set_object)

crunch weak_valid_sched_action[wp]: cap_delete_one weak_valid_sched_action
  (wp: crunch_wps set_thread_state_runnable_weak_valid_sched_action
       set_bound_notification_weak_valid_sched_action maybeM_inv
       mapM_wp' hoare_vcg_if_lift2 hoare_drop_imp
   simp: cur_tcb_def zipWithM_x_mapM unless_def ignore: sched_context_donate set_object)
*)
(*
lemma do_reply_transfer_not_queued:
  "\<lbrace>not_queued t and invs and st_tcb_at active t and scheduler_act_not t and
    K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc |
         clarsimp split del: if_split | wp_once hoare_drop_imps)+
  *)

(*
lemma do_reply_transfer_schedact_not:
  "\<lbrace>scheduler_act_not t and K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc | clarsimp split del: if_split |
         wp_once hoare_drop_imps)+
  *)


end

(*
lemma do_reply_transfer_add_assert:
  assumes a: "\<lbrace>(\<lambda>s. reply_tcb_reply_at (\<lambda>p. p = Some receiver \<longrightarrow>
                                       st_tcb_at awaiting_reply receiver s) rptr s) and P\<rbrace>
               do_reply_transfer sender rptr
              \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> do_reply_transfer sender rptr \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "reply_tcb_reply_at (\<lambda>p. p = Some receiver \<longrightarrow>
                                       st_tcb_at awaiting_reply receiver s) rptr s")
   apply (rule hoare_pre)
    apply (wp a)
   apply simp
  apply (simp add: do_reply_transfer_def maybeM_def liftM_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb x"; clarsimp)
   apply (wpsimp wp: a)
   apply (rule hoare_seq_ext[OF _ gts_sp])
   apply (case_tac state; clarsimp split del: if_split)
    defer 6
    apply (wpsimp+)[7]
defer
   apply (case_tac "x6 = Some receiver"; clarsimp split del: if_split)
    apply (rule_tac Q="\<lambda>_. False" in hoare_weaken_pre)
   apply simp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule sym)
  apply clarsimp
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: get_tcb_def pred_tcb_at_def obj_at_def
                  split: option.splits kernel_object.splits)
  done
*)

(*
weak_if_wp
lemma test_reschedule_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and (\<lambda>s. cur_thread s \<noteq> t)\<rbrace> test_reschedule t \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: test_reschedule_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="ct_not_queued and (\<lambda>s. cur_thread s \<noteq> t) and (\<lambda>s. cur_thread s = cur) and
            (\<lambda>s. scheduler_action s = action) and K (t \<noteq> cur)" in hoare_weaken_pre)
  apply (rule hoare_gen_asm, clarsimp)
defer
apply clarsimp
  apply (case_tac action; clarsimp simp: split del: if_split)
defer 2
  apply wpsimp
  apply wpsimp
  apply wpsimp
  done oops
*)

(* needed by do_reply_transfer_ct_not_queued?
lemma reply_remove_ct_not_queued:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> reply_remove r \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: reply_remove_def assert_opt_def liftM_def)



  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp)
  apply (case_tac "reply_sc reply"; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp simp: pred_tcb_at_def)
  apply (case_tac caller_sc; clarsimp)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
  apply (wpsimp wp: sched_context_donate_ct_not_queued)
*)


crunch cur_thread[wp]: postpone  "\<lambda>s. P (cur_thread s)"
  (wp: dxo_wp_weak hoare_drop_imp ignore: tcb_release_enqueue tcb_sched_action)

context DetSchedSchedule_AI begin

crunch ct_not_queued[wp]: do_ipc_transfer,handle_fault_reply "ct_not_queued::det_state \<Rightarrow> _"
  (wp: mapM_wp' simp: zipWithM_x_mapM)
(*
lemma do_reply_transfer_ct_not_queued:
  "\<lbrace>ct_not_queued and invs and ct_active and scheduler_act_sane\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: do_reply_transfer_def maybeM_def liftM_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac reply)
  apply (case_tac "reply_tcb reply"; clarsimp split del: if_split)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; clarsimp split del: if_split)
         defer 6
         apply (wpsimp+)[7]
  apply (wpsimp wp: hoare_drop_imp simp: thread_set_def)
  *)

(*
crunch cur_thread[wp]: do_reply_transfer "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps maybeM_inv transfer_caps_loop_pres simp: unless_def crunch_simps
   ignore: test_reschedule tcb_sched_action tcb_release_enqueue)
*)
(*
lemma do_reply_transfer_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and ct_active\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: do_reply_transfer_def maybeM_def liftM_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac reply)
  apply (case_tac "reply_tcb reply"; clarsimp split del: if_split)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; clarsimp split del: if_split)
         defer 6
         apply (wpsimp+)[7]
apply (rule hoare_pre)
   apply (wpsimp wp: sch_act_sane_lift set_thread_state_sched_act_not)
 (* apply (clarsimp simp: obj_at_def)
done*) *)

end

locale DetSchedSchedule_AI_handle_hypervisor_fault = DetSchedSchedule_AI +
  assumes handle_hyp_fault_valid_sched[wp]:
    "\<And>t fault.
      \<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
          and (ct_active or ct_idle)\<rbrace>
        handle_hypervisor_fault t fault
      \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_reserved_irq_valid_sched' [wp]:
    "\<And>irq.
      \<lbrace>valid_sched and invs and
         (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
        handle_reserved_irq irq
      \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_hyp_fault_valid_machine_time[wp]:
    "\<And>t fault. handle_hypervisor_fault t fault \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_reserved_irq_valid_machine_time[wp]:
    "\<And>irq. handle_reserved_irq irq \<lbrace>valid_machine_time::det_state \<Rightarrow> _\<rbrace>"

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_interrupt_valid_sched:
  "\<lbrace>valid_sched and invs and valid_machine_time and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_interrupt irq \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  apply (wpsimp wp: get_cap_wp hoare_drop_imps hoare_vcg_all_lift send_signal_valid_sched)
  apply (intro conjI; clarsimp elim!: valid_sched_implies_valid_ipc_qs)
  done

lemma set_scheduler_action_switch_not_cur_thread [wp]:
  "\<lbrace>\<lambda>s. True\<rbrace> set_scheduler_action (switch_thread target) \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  unfolding set_scheduler_action_def
  by wp (simp add: not_cur_thread_def)

lemma possible_switch_to_not_cur_thread [wp]:
  "\<lbrace>not_cur_thread t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. not_cur_thread t\<rbrace>"
  unfolding possible_switch_to_def get_tcb_obj_ref_def
  by (rule hoare_seq_ext[OF _ thread_get_sp]) wpsimp

crunch not_ct[wp]: handle_fault,lookup_reply,lookup_cap,receive_ipc,receive_signal
  "not_cur_thread target::det_state \<Rightarrow> _"
  (wp: mapM_wp' maybeM_inv hoare_drop_imp hoare_vcg_if_lift2 simp: unless_def)

lemma handle_recv_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread target\<rbrace> handle_recv param_a param_b \<lbrace>\<lambda>_. not_cur_thread target::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: handle_recv_def Let_def split del: if_split)
  apply (wpsimp split_del: if_split simp: whenE_def wp: hoare_vcg_if_lift2 hoare_drop_imp)
     apply (rule_tac Q'="\<lambda>_. not_cur_thread target" in hoare_post_imp_R)
      by wpsimp+

crunch it[wp]: handle_fault,lookup_reply,lookup_cap "\<lambda>s. P (idle_thread s)"
  (wp: mapM_wp' maybeM_inv hoare_drop_imp simp: unless_def)

crunch it[wp]: receive_signal "\<lambda>s. P (idle_thread s)"
  (wp: mapM_wp' maybeM_inv hoare_drop_imp hoare_vcg_if_lift2 simp: unless_def)

lemma handle_recv_it[wp]: "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> handle_recv param_a param_b \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (clarsimp simp: handle_recv_def Let_def split del: if_split)
  apply (wpsimp split_del: if_split simp: whenE_def wp: hoare_vcg_if_lift2 hoare_drop_imp)
     apply (rule_tac Q'="\<lambda>_ s. P (idle_thread s)" in hoare_post_imp_R)
      by wpsimp+
(*
lemma refill_budget_check_valid_sched:
  "\<lbrace>valid_sched\<rbrace> refill_budget_check sc_ptr usage capacity \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def refill_full_def)
apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
apply (rule hoare_seq_ext[OF _ assert_sp])
apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (case_tac "capacity=0"; clarsimp)
defer
 apply (wpsimp wp: update_sched_context_valid_sched
refill_budget_check_valid_sched (* not proved *)
hoare_vcg_all_lift hoare_drop_imp
simp: set_refills_def)
apply (intro conjI; clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
active_sc_tcb_at_defs valid_ready_qs_def is_refill_sufficient_def is_refill_ready_def etcb_defs
split: option.splits)
apply fastforce
*)

(*
crunches handle_timeout
for valid_sched[wp]: valid_sched
and not_queued[wp]: "not_queued t"
  (wp: maybeM_inv hoare_drop_imps hoare_vcg_if_lift2)
*)


crunches tcb_release_enqueue
for not_queued[wp]: "not_queued t"
  (wp: hoare_drop_imp mapM_wp')

lemma postpone_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> postpone scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: postpone_def)
  apply (wpsimp simp: tcb_sched_action_def get_sc_obj_ref_def thread_get_def wp: get_sched_context_wp hoare_drop_imp)
  by (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def split: option.splits)

crunches set_extra_badge
  for ct_active[wp]: "ct_active::det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps dxo_wp_weak simp: cap_insert_ext_def)

lemma set_mrs_ct_active[wp]:
  "set_mrs thread buf msgs \<lbrace>ct_active::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_mrs_def store_word_offs_def
  supply if_split [split del]
  apply (wpsimp simp: zipWithM_x_mapM wp: mapM_wp' set_object_wp)
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD
               split: if_splits)

lemma set_message_info_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_. ct_active\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def ct_in_state_def split_def set_object_def)

crunches do_normal_transfer, do_fault_transfer
  for ct_active[wp]: "ct_active::det_state \<Rightarrow> _"
  (simp: zipWithM_x_mapM wp: mapM_wp' transfer_caps_loop_pres)

(* do we need these?
lemma send_ipc_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     send_ipc True False badge True False thread epptr
       \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
   apply (clarsimp simp: send_ipc_def)
  by (wpsimp simp: send_ipc_def set_simple_ko_def a_type_def partial_inv_def
      wp: set_object_wp get_object_wp sts_st_tcb_at' hoare_vcg_all_lift hoare_drop_imp)

lemma end_timeslice_ct_active:
  "\<lbrace>ct_active\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: end_timeslice_def)
*)

lemma reschedule_required_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     reschedule_required \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+


(* do we actually need all these ?
lemma send_ipc_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
     send_ipc block call badge can_grant can_donate thread epptr
        \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp)
    apply (case_tac block; clarsimp)
     apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
    apply wpsimp
   apply (case_tac block; clarsimp)
    apply (wpsimp wp: set_thread_state_sched_act_not_valid_sched)
   apply wpsimp

  apply (rename_tac ep_queue)
  apply (case_tac ep_queue; clarsimp)
  apply (rule hoare_seq_ext)
  apply (rule hoare_seq_ext[OF _ gts_sp])
apply (case_tac recv_state; clarsimp simp: bind_assoc maybeM_def)
apply (rename_tac ep reply)
apply (case_tac reply; clarsimp)


lemma send_fault_ipc_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     send_fault_ipc tptr handler_cap fault can_donate \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wpsimp simp: thread_set_def set_object_def)
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def
 dest!: get_tcb_SomeD split: option.splits)
  done

lemma handle_timeout_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     handle_timeout tptr f \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: handle_timeout_def)

lemma postpone_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     postpone tptr \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: postpone_def wp: hoare_drop_imp)

lemma end_timeslice_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     end_timeslice canTimeout \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: end_timeslice_def)

crunches end_timeslice
for cur_thred[wp]: "\<lambda>s::det_state. P (cur_thread s)"

lemma end_timeslice_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     end_timeslice canTimeout \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma set_refills_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     set_refills scptr new \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma set_refills_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     set_refills scptr new \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_refills_def)

lemma update_sc_refills_active_sc_tcb_at_merge:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
     update_sched_context scptr (sc_refills_update (min_budget_merge b)) \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  by (intro conjI impI, clarsimp, rule_tac x=scp in exI, fastforce)

crunches refill_full
for active_sc_tcb_at[wp]: "active_sc_tcb_at t"


lemma refill_budget_check_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     refill_budget_check sc_ptr usage \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: Let_def refill_budget_check_def split_del: if_split)

lemma refill_budget_check_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     refill_budget_check sc_ptr usage capacity \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2 update_sc_refills_active_sc_tcb_at_merge
               simp: Let_def refill_budget_check_def)

lemma charge_budget_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: charge_budget_def Let_def)

lemma charge_budget_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma check_budget_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace> check_budget \<lbrace>\<lambda>_ s::det_state. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  by (wpsimp wp: hoare_vcg_if_lift2 get_sched_context_wp hoare_vcg_all_lift hoare_drop_imp)
*)

lemma check_budget_restart_valid_sched:
  "\<lbrace>valid_sched and invs and ct_not_in_release_q and ct_not_queued and schact_is_rct
    and ct_ARS and (\<lambda>s. valid_refills (cur_sc s) s)\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>rv s::det_state. rv \<longrightarrow> valid_sched s\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (wpsimp wp: gts_wp hoare_vcg_all_lift)
   apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2 check_budget_valid_sched)
  apply (simp)
  apply (intro conjI; fastforce elim!: invs_cur_sc_chargeableE)
  done

(* FIXME: this should replace existing, weaker, lemma *)
lemma update_sc_consumed_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
   update_sched_context csc (sc_consumed_update (\<lambda>_. consumed))
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift
                 budget_ready_update_sched_context_no_change
                 budget_sufficient_update_sched_context_no_change
                 active_sc_tcb_at_update_sched_context_no_change)

lemma handle_yield_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and ct_not_in_release_q and ct_not_queued and
    cur_sc_tcb and scheduler_act_sane and ct_ARS and (\<lambda>s. valid_refills (cur_sc s) s)
    and cur_sc_chargeable\<rbrace>
   handle_yield
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_yield_def
  apply (wpsimp simp: set_sc_obj_ref_def wp: charge_budget_valid_sched)
  apply (erule valid_sched_implies_valid_ipc_qs)
  done

(*
context begin
 private method handle_event_valid_sched_cases =
(     (rule hoare_seq_ext),
      (rule_tac Q="invs and ct_active and valid_sched
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
               and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)" in hoare_weaken_pre),
       (rule hoare_seq_ext[rotated]),
        (rule hoare_pre),
         (rule hoare_vcg_conj_lift[OF
                      check_budget_restart_invs
                      hoare_vcg_conj_lift[OF
                        check_budget_restart_valid_sched
                        hoare_vcg_conj_lift[OF
                          check_budget_restart_sched_action[where P="(=) resume_cur_thread"]
                          check_budget_restart_ct_active]]]),
        clarsimp,
       (rename_tac restart),
       (case_tac restart; clarsimp simp: whenE_def),
        (wpsimp wp: handle_fault_valid_sched handle_invocation_valid_sched handle_recv_valid_sched'
              simp: valid_sched_ct_not_queued),
       (clarsimp simp: ct_in_state_def valid_fault_def),
       wpsimp,
      simp,
     (wpsimp wp: update_time_stamp_valid_sched update_time_stamp_invs update_time_stamp_pred_tcb_at))
*)
lemma handle_event_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s) \<comment> \<open>and simple_sched_action\<close>\<rbrace>
   handle_event e
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases e, simp_all)
       apply (rename_tac syscall)
       apply (case_tac syscall, simp_all add: handle_send_def handle_call_def liftE_bindE)
                 prefer 16
                 apply wp
                 apply (fastforce  simp: ct_in_state_def intro: valid_sched_ct_not_queued)
(*                apply (handle_event_valid_sched_cases+)[11]
     apply (simp add: liftE_def bind_assoc, handle_event_valid_sched_cases)+

  (* UnknownSyscall *)
   apply (simp add: liftE_def bind_assoc)
   apply (rule hoare_seq_ext)
    apply (rule hoare_seq_ext)
     apply (rule_tac Q="invs and ct_active and valid_sched
               and (\<lambda>s. scheduler_action s = resume_cur_thread)
(*               and simple_sched_action*)
               and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)" in hoare_weaken_pre)
      apply (rule hoare_seq_ext[rotated])
       apply (rule hoare_pre)
        apply (rule hoare_vcg_conj_lift[OF
        check_budget_invs
        hoare_vcg_conj_lift[OF
          check_budget_valid_sched
          hoare_vcg_conj_lift[OF
            check_budget_true
            check_budget_ct_active]]])
       apply (clarsimp simp: )
      apply (wpsimp wp: )*)
  sorry (* handle_event_valid_sched *)
(*
end
*)
crunch valid_list[wp]: activate_thread valid_list (wp: hoare_drop_imp)
crunch valid_list[wp]: guarded_switch_to, switch_to_idle_thread, choose_thread valid_list
  (wp: crunch_wps)

end

lemma next_domain_valid_dlist[wp]:
  "next_domain \<lbrace>valid_list\<rbrace>"
  unfolding next_domain_def Let_def
  apply (fold reset_work_units_def)
  apply (wpsimp | simp add: reset_work_units_def)+
  done

crunch valid_list[wp]: switch_sched_context,set_next_interrupt valid_list (wp: hoare_drop_imp)

lemma sc_and_timer_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> sc_and_timer \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by (wpsimp simp: sc_and_timer_def)


context DetSchedSchedule_AI_handle_hypervisor_fault begin

crunch valid_list[wp]: schedule_choose_new_thread valid_list

crunch valid_list[wp]: awaken valid_list
  (wp: crunch_wps get_object_wp)

lemma schedule_valid_list[wp]: "\<lbrace>valid_list\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: Schedule_A.schedule_def)
  apply (wp add: tcb_sched_action_valid_list alternative_wp select_wp gts_wp hoare_drop_imps
                 is_schedulable_wp hoare_vcg_all_lift
         | wpc | simp)+
  done

lemma call_kernel_valid_list[wp]: "\<lbrace>valid_list\<rbrace> call_kernel e \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: call_kernel_def)
  by (wpsimp wp: is_schedulable_wp hoare_drop_imps hoare_vcg_all_lift)+

crunches update_sk_obj_ref
for valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
 (wp: crunch_wps hoare_drop_imp simp: crunch_simps)

lemma reply_unlink_tcb_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tp\<rbrace>
     reply_unlink_tcb tp rp
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: set_thread_state_not_queued_valid_release_q gts_wp get_simple_ko_wp)

lemma tcb_ready_time_sc_replies_update[simp]:
  "\<lbrakk>active_sc_tcb_at x s; kheap s ref = Some (SchedContext sc n)\<rbrakk> \<Longrightarrow>
     tcb_ready_time x
            (s\<lparr>kheap := kheap s(ref \<mapsto> SchedContext (sc\<lparr>sc_replies := list\<rparr>) n)\<rparr>)
        = tcb_ready_time x s"
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_rev get_tcb_def
                  split: option.splits if_splits kernel_object.splits)

lemma reply_remove_tcb_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tp\<rbrace>
   reply_remove_tcb tp rp \<lbrace> \<lambda>_. valid_release_q:: det_state \<Rightarrow> _ \<rbrace>"
  apply (clarsimp simp: reply_remove_tcb_def)
  by (wpsimp wp: get_simple_ko_wp hoare_drop_imp update_sched_context_valid_release_q)

(*
lemma reply_unlink_tcb_sorted_release_q[wp]:
  "\<lbrace> sorted_release_q and valid_release_q and not_in_release_q tp\<rbrace>
     reply_unlink_tcb tp rp
   \<lbrace> \<lambda>_. sorted_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: gts_wp get_simple_ko_wp)

lemma reply_remove_tcb_sorted_release_q[wp]:
  "\<lbrace> sorted_release_q and valid_release_q and not_in_release_q tp\<rbrace>
     reply_remove_tcb tp rp
   \<lbrace> \<lambda>_. sorted_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_tcb_def)
  by (wpsimp wp: hoare_drop_imp get_simple_ko_wp)
*)
lemma blocked_cancel_ipc_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tptr\<rbrace>
     blocked_cancel_ipc state tptr reply_opt
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: blocked_cancel_ipc_def)
  by (wpsimp wp: set_thread_state_not_queued_valid_release_q hoare_drop_imp)
(*
lemma update_waiting_ntfn_valid_release_q[wp]:
  "\<lbrace> valid_release_q\<rbrace>
     update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: update_waiting_ntfn_def)
  by (wpsimp wp: set_thread_state_not_queued_valid_release_q hoare_drop_imp hoare_vcg_all_lift)
*)
(*
lemma blocked_cancel_ipc_sorted_release_q[wp]:
  "\<lbrace> sorted_release_q and valid_release_q and not_in_release_q tptr\<rbrace>
     blocked_cancel_ipc state tptr reply_opt
   \<lbrace> \<lambda>_. sorted_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: blocked_cancel_ipc_def)
  by (wpsimp wp: set_thread_state_sorted_release_q hoare_drop_imp)
*)
(*
crunches update_waiting_ntfn
for valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
(*and sorted_release_q[wp]: "sorted_release_q::det_state \<Rightarrow> _"*)
 (wp: crunch_wps valid_release_q_lift
  simp: Let_def crunch_simps)

crunches blocked_cancel_ipc, update_waiting_ntfn, send_signal
for valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
(*and sorted_release_q[wp]: "sorted_release_q::det_state \<Rightarrow> _"*)
 (wp: crunch_wps get_simple_ko_wp hoare_drop_imp hoare_vcg_all_lift maybeM_wp transfer_caps_loop_pres
  simp: Let_def crunch_simps)
*)

(*
crunches end_timeslice
for cur_tcb[wp]: "cur_tcb::det_state \<Rightarrow> _"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
 (wp: crunch_wps get_simple_ko_wp hoare_drop_imp hoare_vcg_all_lift maybeM_wp
  simp: Let_def crunch_simps)


crunches handle_interrupt
for cur_tcb[wp]: "cur_tcb::det_state \<Rightarrow> _"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
(*and sorted_release_q[wp]: "sorted_release_q::det_state \<Rightarrow> _"*)
 (wp: crunch_wps get_simple_ko_wp hoare_drop_imp hoare_vcg_all_lift maybeM_wp
  simp: Let_def crunch_simps)
*)

crunches handle_interrupt
for ct_active[wp]: "ct_active::det_state \<Rightarrow> _"

lemma call_kernel_valid_sched_helper:
  "\<lbrace>\<lambda>s. (valid_sched and invs and
         (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)) s \<and>
        invs s \<and> valid_machine_time s \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) s \<and>
         schact_is_rct s \<and> cur_sc_chargeable s\<rbrace>
\<comment> \<open>
         (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s
                          \<and> ct_not_in_release_q s)) s \<and>
        invs s \<and> bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
\<close>
   check_budget
   \<lbrace>\<lambda>_ s::det_state.
           valid_sched s \<and>
           invs s \<and>
           valid_machine_time s \<and>
           (the irq \<in> non_kernel_IRQs \<longrightarrow>
            scheduler_act_sane s \<and> ct_not_queued s \<and> ct_not_in_release_q s) \<and>
           invs s\<rbrace>"
   apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def) (* FIXME RT *)
   apply (wpsimp wp: hoare_vcg_conj_lift reschedule_valid_sched_const get_sched_context_wp
                     hoare_drop_imps hoare_vcg_all_lift charge_budget_invs charge_budget_valid_sched)
   by (clarsimp simp: schact_is_rct_def valid_sched_implies_valid_ipc_qs)

lemma call_kernel_valid_sched_charge_budget_helper:
  "\<lbrace>\<lambda>s. (valid_sched and invs and
         (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)) s \<and>
        invs s \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) s \<and>
        valid_machine_time s \<and> cur_sc_chargeable s \<and>
        scheduler_act_sane s\<rbrace>
   charge_budget consumed False
   \<lbrace>\<lambda>_ s::det_state.
           valid_sched s \<and>
           invs s \<and>
           valid_machine_time s \<and>
           (the irq \<in> non_kernel_IRQs \<longrightarrow>
            scheduler_act_sane s \<and> ct_not_queued s) \<and>
           invs s\<rbrace>"
   apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def) (* FIXME RT *)
   apply (wpsimp wp: hoare_vcg_conj_lift reschedule_valid_sched_const get_sched_context_wp
                     hoare_drop_imps hoare_vcg_all_lift charge_budget_invs charge_budget_valid_sched)
   apply (erule valid_sched_implies_valid_ipc_qs)
   done

lemma valid_refills_ignores_machine_state[simp]:
  "valid_refills x (s\<lparr>machine_state := j\<rparr>) = valid_refills x s"
  by (clarsimp simp: valid_refills_def)

crunches handle_fault, reply_from_kernel, check_budget_restart, lookup_reply, lookup_cap
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"

crunches receive_ipc, receive_signal, send_signal
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma handle_interrupt_valid_machine_time[wp]:
  "handle_interrupt irq \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  by (wpsimp simp: do_machine_op_bind wp: hoare_drop_imp)

lemma do_reply_transfer_valid_machine_time[wp]:
  "do_reply_transfer a b \<lbrace>valid_machine_time :: det_state \<Rightarrow> _\<rbrace>"
  unfolding do_reply_transfer_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)

lemma preemption_point_valid_machine_time[wp]:
  "preemption_point \<lbrace>valid_machine_time\<rbrace>"
  unfolding preemption_point_def
  apply (wpsimp simp: OR_choiceE_def)
        apply (clarsimp simp: valid_machine_time_def)
       apply (wpsimp simp: do_extended_op_def reset_work_units_def)+
  done

crunches cap_delete, delete_objects
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_vcg_all_lift ignore: do_machine_op)

crunches cap_revoke, install_tcb_cap
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps cap_revoke_preservation check_cap_inv)

crunches cap_move, cap_swap, cancel_badged_sends, set_domain
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: filterM_preserved)

crunches invoke_sched_context, invoke_sched_control_configure, invoke_tcb, invoke_irq_handler
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv ignore: do_machine_op)

crunches invoke_irq_control, invoke_cnode, invoke_domain, invoke_tcb
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps ignore: do_machine_op)

crunches create_cap, retype_region, reset_untyped_cap, invoke_untyped
  for valid_machine_time[wp]: "valid_machine_time :: det_state \<Rightarrow> _"
  (wp: crunch_wps mapME_x_wp_inv ignore: do_machine_op)

lemma perform_invocation_valid_machine_time[wp]:
  "perform_invocation a b c iv \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  by (case_tac iv; wpsimp)

lemma handle_invocation_valid_machine_time[wp]:
  "handle_invocation a b c d e \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
  by (wpsimp wp: hoare_drop_imp simp: lookup_cap_and_slot_def)

lemma valid_machine_time_irq_state[simp]:
  "valid_machine_time_2 (cur_time s) (machine_state s\<lparr>irq_state := k\<rparr>) =
   valid_machine_time s"
  by (clarsimp simp: valid_machine_time_def)

crunches handle_vm_fault
  for valid_machine_time[wp]: "valid_machine_time:: det_state \<Rightarrow> _"

lemma update_time_stamp_ct_ARS[wp]:
 "\<lbrace>ct_ARS and valid_machine_time :: det_state \<Rightarrow> _\<rbrace> update_time_stamp \<lbrace>\<lambda>_. ct_ARS\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>t. t = cur_thread s \<and> active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s"
   in hoare_strengthen_post)
  by (wp hoare_vcg_ex_lift | simp)+

lemma handle_event_valid_machine_time[wp]:
  "handle_event e \<lbrace>valid_machine_time:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
  subgoal for sc
    apply (case_tac sc; simp)
              apply (wpsimp simp: handle_call_def handle_recv_def Let_def handle_send_def
                                  handle_yield_def
                              wp: hoare_drop_imps)+
    done
      apply wpsimp+
  done

lemma update_time_stamp_valid_sched[wp]:
 "\<lbrace>valid_sched and valid_machine_time :: det_state \<Rightarrow> _\<rbrace> update_time_stamp \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_lift_pre_conj[where R = valid_machine_time])

crunches update_time_stamp
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"

lemma update_time_stamp_valid_refills[wp]:
  "update_time_stamp \<lbrace>\<lambda>s. valid_refills t s\<rbrace>"
  unfolding update_time_stamp_def
  apply (wpsimp simp: do_machine_op_def)
  by (clarsimp simp: valid_refills_def)

lemma update_time_stamp_valid_refills_cur_sc[wp]:
  "update_time_stamp \<lbrace>\<lambda>s. valid_refills (cur_sc s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps, wpsimp, simp)

lemma call_kernel_valid_sched:
  "\<lbrace>\<lambda>s. invs s \<and> valid_sched s \<and> (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) s \<and> (ct_active or ct_idle) s
        \<and> scheduler_action s = resume_cur_thread
        \<and> is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s
        \<and> bound_sc_tcb_at bound (cur_thread s) s \<and> valid_refills (cur_sc s) s
        \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> ct_ARS s \<and> valid_machine_time s\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp schedule_valid_sched activate_thread_valid_sched handle_interrupt_valid_sched | simp)+
(*          apply (rule_tac Q="\<lambda>rv. invs" in hoare_strengthen_post[rotated])
           apply (erule invs_valid_idle)
          apply wp
         apply (wp is_schedulable_wp)
          apply (wp call_kernel_check_budget_helper)
         apply (wp call_kernel_valid_sched_charge_budget_helper)
        apply (wp is_schedulable_wp)+
(*
     apply (rule_tac Q="\<lambda>_. valid_sched and invs and ct_not_in_release_q and ct_not_queued
                            and valid_machine_time and (\<lambda>s. valid_refills (cur_sc s) s)
                            and scheduler_act_sane and cur_sc_chargeable" in hoare_strengthen_post)
      apply (wpsimp wp: scheduler_act_sane_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (clarsimp simp: invs_def)
*)
     apply (rule_tac Q="\<lambda>_. valid_sched and invs and ct_not_in_release_q and ct_not_queued
                            and schact_is_rct and ct_schedulable and valid_machine_time and (\<lambda>s. valid_refills (cur_sc s) (- 1) s)" in hoare_strengthen_post)
      apply wpsimp
     apply (auto simp: schact_is_rct_def)[1]
(*
  apply (wpsimp wp: schedule_valid_sched activate_thread_valid_sched
  hoare_vcg_ball_lift
               simp: valid_sched_valid_release_q)
      apply (rule_tac Q="\<lambda>rv. invs" in hoare_strengthen_post)
       apply wp
      apply (erule invs_valid_idle)
     apply (wp call_kernel_valid_sched_helper)
*)
    apply (rule hoare_strengthen_post
      [where Q="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> valid_sched s \<and> invs s \<and> valid_machine_time s
                        \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) s
                        \<and> scheduler_act_sane s \<and> (cur_sc_chargeable s)"])
     apply (wpsimp wp: getActiveIRQ_neq_non_kernel)
     apply (clarsimp simp: cur_sc_chargeable_def)
    apply fastforce
   apply (rule_tac Q="\<lambda>rv s. valid_sched s \<and> invs s" and
(*
                   E="\<lambda>rv s. (ct_not_in_release_q s \<and> valid_machine_time s \<and>
                              ct_not_queued s \<and> scheduler_act_sane s \<and> cur_sc_chargeable s \<and>
                              valid_refills (cur_sc s) s) \<and> (valid_sched s \<and> invs s)"
           in hoare_post_impErr)
*)
(*
                   E="\<lambda>rv s. (ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) (- 1) s \<and>
                              schact_is_rct s \<and> ct_schedulable s \<and> valid_machine_time s) \<and>
                             valid_sched s \<and> invs s" in hoare_post_impErr)
      E="\<lambda>rv s. (ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) 0 s \<and> schact_is_rct s \<and> ct_schedulable s \<and> valid_machine_time s) \<and> valid_sched s \<and> invs s" in hoare_post_impErr)
     apply (rule hoare_vcg_E_conj[rotated])
      apply (rule valid_validE)
      apply (wpsimp wp: handle_event_valid_sched)
     apply (wpsimp wp: handle_event_ct_not_in_release_qE_E
                       handle_event_ct_not_queuedE_E
                       handle_event_scheduler_act_sane)
    apply (clarsimp simp: invs_def valid_state_def)
   apply (clarsimp simp: invs_def valid_state_def)
(*
  apply (clarsimp simp: is_schedulable_bool_def2)
  apply (intro conjI impI)
      apply (rule valid_sched_implies_valid_ipc_qs, simp)+
     apply (erule invs_cur_sc_chargeableE, simp add: schact_is_rct_def)
    apply (clarsimp simp: ct_in_state_def obj_at_def cur_tcb_def is_tcb pred_tcb_at_def)+
*)
  apply (clarsimp simp: schact_is_rct_def is_schedulable_bool_def2)
  apply (clarsimp simp: ct_in_state_def obj_at_def cur_tcb_def is_tcb pred_tcb_at_def)
*)
      E="\<lambda>rv s. valid_sched s \<and> invs s" in hoare_post_impErr)
     apply (rule valid_validE)
     apply (wp handle_event_valid_sched)
    apply clarsimp+
(*  subgoal for s
    apply (insert ct_assumptions[where s=s])
    apply (clarsimp simp: pred_tcb_at_def obj_at_def invs_cur)
    done
  subgoal for e s
    apply (insert ct_assumptions[where s=s])
    apply (elim conjE; frule invs_valid_objs, frule invs_sym_refs, frule invs_cur)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def cur_tcb_def is_tcb pred_tcb_at_def)
    apply (drule (2) sc_tcb_not_idle_thread_helper)
    apply (clarsimp simp: state_refs_of_def get_refs_def2)
    done
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done
*)*) sorry (* call_kernel_valid_sched *)
end

end
