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
  do_ipc_transfer_cur_thread
  machine_ops_last_machine_time
  handle_arch_fault_reply_typ_at
end

lemmas [wp] =
  do_ipc_transfer_cur_thread
  handle_arch_fault_reply_typ_at
  machine_ops_last_machine_time

(* FIXME: move *)
lemma hoare_drop_assertion:
  assumes "\<lbrace>\<lambda>s. P s \<longrightarrow> Q s\<rbrace> f \<lbrace>R\<rbrace>"
  shows "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>"
  by (wpsimp wp: assms)

lemma current_time_bounded_strengthen:
  "current_time_bounded_2 k a \<Longrightarrow> n \<le> k \<Longrightarrow> current_time_bounded_2 n a"
  unfolding current_time_bounded_def
  by (erule order_trans[rotated], clarsimp)

lemma valid_sched_released_ipc_queues[elim!]:
  "valid_sched s \<Longrightarrow> released_ipc_queues s"
  by (simp add: valid_sched_def)

lemma as_user_cur_sc_chargeable[wp]:
  "as_user f d \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding as_user_def cur_sc_chargeable_def2
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_at_pred_def dest!: get_tcb_SomeD)
  apply (case_tac "cur_thread s = f"; simp)
  apply fastforce
  by fastforce

definition
  "cur_sc_is_sc s \<equiv> obj_at (\<lambda>ko. case ko of SchedContext sc n \<Rightarrow> True | _ \<Rightarrow> False) (cur_sc s) s"

lemma machine_time_of_s[simp]:
  "last_machine_time_of (detype S s) = last_machine_time_of s"
  by (clarsimp simp: detype_def)

lemma cur_time_no_overflow:
  "valid_machine_time s \<Longrightarrow> cur_time s \<le> cur_time s + kernelWCET_ticks"
  apply (rule no_plus_overflow_neg)
  apply (rule word_leq_minus_one_le)
   using kernelWCET_ticks_non_zero apply simp
  apply (erule cur_time_bounded)
  done

lemma is_round_robin_wp:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow> Q (sc_period sc = sc_budget sc) s\<rbrace>
    is_round_robin scp
   \<lbrace>Q\<rbrace>" by (wpsimp simp: is_round_robin_def)

(* FIXME RT: replace is_round_robin_wp with this version. *)
lemma is_round_robin_wp':
  "\<lbrace>\<lambda>s. \<forall>scrc. pred_map_eq scrc (sc_refill_cfgs_of s) scp \<longrightarrow> Q (scrc_period scrc = scrc_budget scrc) s\<rbrace>
    is_round_robin scp
   \<lbrace>Q\<rbrace>" by (wpsimp wp: is_round_robin_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

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
  by (wpsimp wp: set_tcb_queue_wp
           simp: tcb_sched_action_def etcb_at_def thread_get_def)

lemma update_sched_context_sc_tcb_sc_at:
  assumes f_act_triv: "sc_ptr = sc_ptr' \<Longrightarrow> \<forall>x. P (sc_tcb (f x)) = P (sc_tcb x)"
  shows "update_sched_context sc_ptr f \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr' s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (case_tac "sc_ptr = sc_ptr'"; clarsimp simp: obj_at_def sc_at_pred_n_def f_act_triv)
  done

\<comment> \<open>Rules that completely describe the behaviour of functions w.r.t. the aspects of
    state relevant to valid_sched. They should be phrased with a postcondition that
    is at least as general as "valid_sched_pred P", for arbitrary P, and a precondition
    that can be written as "valid_sched_pred (f P)", for some f.\<close>

named_theorems valid_sched_wp

\<comment> \<open>Rules useful for simplifying goals resulting from valid_sched_wp rules.\<close>

named_theorems valid_sched_wpsimps

lemmas [valid_sched_wpsimps] =
  valid_sched_def obj_at_kh_kheap_simps

\<comment> \<open>tcb_sched_action\<close>

abbreviation tcb_sched_ready_q_update where
  "tcb_sched_ready_q_update domain prio action \<equiv>
    \<lambda>qs d p. if d = domain \<and> p = prio then action (qs domain prio) else qs d p"

lemma tcb_sched_action_wp[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>dom prio. etcb_eq' prio dom (etcbs_of s) thread
                   \<longrightarrow> Q (ready_queues_update (tcb_sched_ready_q_update dom prio (action thread)) s)\<rbrace>
   tcb_sched_action action thread
   \<lbrace>\<lambda>_. Q\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def wp: thread_get_wp' set_tcb_queue_wp)
     (auto simp: obj_at_def vs_all_heap_simps elim!: rsubst[of Q])

lemma tcb_sched_action_valid_sched_misc[wp]:
  "tcb_sched_action act t \<lbrace>\<lambda>s. P (consumed_time s) (cur_time s) (cur_domain s) (cur_thread s) (cur_sc s)
                                 (idle_thread s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
                                 (kheap s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

abbreviation (input) tcb_sched_enqueue_valid_ready_qs_update where
  "tcb_sched_enqueue_valid_ready_qs_update domain prio thread queues ct etcbs tcb_sts
                                                  tcb_scps sc_refill_cfgs \<equiv>
    valid_ready_qs_2 queues ct etcbs tcb_sts tcb_scps sc_refill_cfgs
     \<and> (thread \<in> set (queues domain prio)
         \<or> (etcb_eq' prio domain etcbs thread
             \<and> pred_map runnable tcb_sts thread
             \<and> released_sc_tcb_at_pred ct tcb_scps sc_refill_cfgs thread))"

lemma tcb_sched_action_valid_ready_qs_simps[valid_sched_wpsimps]:
  shows "valid_ready_qs_2 (tcb_sched_ready_q_update domain prio (tcb_sched_enqueue thread) queues)
                          ct etcbs tcb_sts tcb_scps sc_refill_cfgs
         \<longleftrightarrow> tcb_sched_enqueue_valid_ready_qs_update domain prio thread queues ct etcbs tcb_sts
                                                     tcb_scps sc_refill_cfgs"
  and "valid_ready_qs_2 (tcb_sched_ready_q_update domain prio (tcb_sched_append thread) queues)
                        ct etcbs tcb_sts tcb_scps sc_refill_cfgs
       \<longleftrightarrow> tcb_sched_enqueue_valid_ready_qs_update domain prio thread queues ct etcbs tcb_sts
                                                   tcb_scps sc_refill_cfgs"
  and "valid_ready_qs_2 queues ct etcbs tcb_sts tcb_scps sc_refill_cfgs
       \<Longrightarrow> valid_ready_qs_2 (tcb_sched_ready_q_update domain prio (tcb_sched_dequeue thread) queues)
                            ct etcbs tcb_sts tcb_scps sc_refill_cfgs"
  by (auto simp: valid_ready_qs_def tcb_sched_enqueue_def tcb_sched_append_def tcb_sched_dequeue_def)

lemma tcb_sched_enqueue_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and released_sc_tcb_at thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps released_sc_tcb_at_def)

lemma tcb_sched_append_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and active_sc_tcb_at thread
     and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps released_sc_tcb_at_def)

lemma tcb_sched_enqueue_in_ready_q[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. in_ready_q thread\<rbrace>"
  by (wpsimp wp: tcb_sched_action_wp)
     (auto simp: vs_all_heap_simps in_queues_2_def tcb_sched_enqueue_def)

lemma tcb_sched_append_in_ready_q[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. in_ready_q thread\<rbrace>"
  by (wpsimp wp: tcb_sched_action_wp)
     (auto simp: vs_all_heap_simps in_queues_2_def tcb_sched_append_def)

(* this is not safe! *)
(* if in_ready_q thread then this will break valid_blocked  *)
lemma tcb_sched_dequeue_valid_ready_qs:
  "\<lbrace>valid_ready_qs\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_act_set_simps[valid_sched_wpsimps]:
  "t \<in> set (tcb_sched_enqueue thread queue) = (t \<in> set queue \<or> t = thread)"
  "t \<in> set (tcb_sched_append thread queue) = (t \<in> set queue \<or> t = thread)"
  "t \<in> set (tcb_sched_dequeue thread queue) = (t \<in> set queue \<and> t \<noteq> thread)"
  by (auto simp: tcb_sched_enqueue_def tcb_sched_append_def tcb_sched_dequeue_def)

lemma tcb_sched_act_in_queues_2_simps[valid_sched_wpsimps]:
  "in_queue_2 (tcb_sched_enqueue thread queue) t \<longleftrightarrow> t = thread \<or> in_queue_2 queue t"
  "in_queue_2 (tcb_sched_append thread queue) t \<longleftrightarrow> t = thread \<or> in_queue_2 queue t"
  "in_queue_2 (tcb_sched_dequeue thread queue) t \<longleftrightarrow> t \<in> set queue \<and> t \<noteq> thread"
  by (auto simp: in_queue_2_def valid_sched_wpsimps)

lemma tcb_sched_ready_q_update_set_simps[valid_sched_wpsimps]:
  "t \<in> set (tcb_sched_ready_q_update domain prio (tcb_sched_enqueue thread) queues d p)
   = (t \<in> set (queues d p) \<or> (d = domain \<and> p = prio \<and> t = thread))"
  "t \<in> set (tcb_sched_ready_q_update domain prio (tcb_sched_append thread) queues d p)
   = (t \<in> set (queues d p) \<or> (d = domain \<and> p = prio \<and> t = thread))"
  "t \<in> set (tcb_sched_ready_q_update domain prio (tcb_sched_dequeue thread) queues d p)
   = (t \<in> set (queues d p) \<and> (t,d,p) \<noteq> (thread,domain,prio))"
  by (auto simp: valid_sched_wpsimps)

lemma tcb_sched_ready_q_update_in_queues_2_simps[valid_sched_wpsimps]:
  "in_queues_2 (tcb_sched_ready_q_update domain prio (tcb_sched_enqueue thread) queues) t
   \<longleftrightarrow> t = thread \<or> in_queues_2 queues t"
  "in_queues_2 (tcb_sched_ready_q_update domain prio (tcb_sched_append thread) queues) t
   \<longleftrightarrow> t = thread \<or> in_queues_2 queues t"
  "in_queues_2 (tcb_sched_ready_q_update domain prio (tcb_sched_dequeue thread) queues) t
   \<longleftrightarrow> (\<exists>d p. t \<in> set (queues d p) \<and> (t,d,p) \<noteq> (thread,domain,prio))"
  by (auto simp: in_queues_2_def valid_sched_wpsimps)

lemma tcb_sched_action_ct_not_in_q_simps[valid_sched_wpsimps]:
  assumes "ct_not_in_q_2 queues sa ct"
  shows tcb_sched_enqueue_not_in_q_simp:
    "not_cur_thread_2 thread sa ct \<Longrightarrow> ct_not_in_q_2 (tcb_sched_ready_q_update domain prio
                                                     (tcb_sched_enqueue thread) queues) sa ct"
  and tcb_sched_append_not_in_q_simp:
    "not_cur_thread_2 thread sa ct \<Longrightarrow> ct_not_in_q_2 (tcb_sched_ready_q_update domain prio
                                                     (tcb_sched_append thread) queues) sa ct"
  and tcb_sched_dequeue_not_in_q_simp:
    "ct_not_in_q_2 (tcb_sched_ready_q_update domain prio (tcb_sched_dequeue thread) queues) sa ct"
  using assms by (auto simp: ct_not_in_q_2_def not_cur_thread_2_def valid_sched_wpsimps not_queued_2_def)

lemma tcb_sched_enqueue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_append_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_dequeue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma valid_blocked_discharge_except:
  assumes "valid_blocked_thread id id S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  shows "valid_blocked_except_set_2 (insert t S) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
         \<longleftrightarrow> valid_blocked_except_set_2 S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  using assms by (auto simp: valid_blocked_defs)

lemmas valid_blocked_discharge_except'
  = valid_blocked_discharge_except[unfolded valid_blocked_thread_def]

(* valid_blocked_except_set doesn't say much; S can contain anything that is not blocked *)
(* see also valid_blocked_except_set_subset *)
(* use in conjunction with valid_sched_except_blocked *)
lemmas valid_blocked_except_set_less
  = valid_blocked_discharge_except'[THEN iffD1, rotated]

lemma tcb_sched_insert_valid_blocked_simps[valid_sched_wpsimps]:
  "valid_blocked_except_set_2 S (tcb_sched_ready_q_update domain prio (tcb_sched_enqueue thread) queues)
                                    rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
    \<longleftrightarrow> valid_blocked_except_set_2 (insert thread S) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  "valid_blocked_except_set_2 S (tcb_sched_ready_q_update domain prio (tcb_sched_append thread) queues)
                                    rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
    \<longleftrightarrow> valid_blocked_except_set_2 (insert thread S) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  by (auto simp: valid_blocked_defs valid_sched_wpsimps)

lemma tcb_sched_dequeue_valid_blocked_simp:
  assumes "T \<subseteq> S"
  assumes "valid_blocked_except_set_2 T queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes "valid_blocked_thread Not id S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  shows "valid_blocked_except_set_2 S (tcb_sched_ready_q_update domain prio (tcb_sched_dequeue t) queues)
                                    rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  using assms by (auto simp: valid_blocked_thread_def in_queues_2_def valid_sched_wpsimps
                      elim!: valid_blockedE)

\<comment> \<open>Use more concrete T and S to avoid simplifier slow-down\<close>
lemmas tcb_sched_dequeue_valid_blocked_simps[valid_sched_wpsimps] =
  tcb_sched_dequeue_valid_blocked_simp[OF subset_refl]
  tcb_sched_dequeue_valid_blocked_simp[where T=S for S, OF subset_insertI[where a=t' for t'], simplified]

lemmas tcb_sched_dequeue_valid_blocked_bot_simps[valid_sched_wpsimps] =
  tcb_sched_dequeue_valid_blocked_simps[OF _ valid_blocked_thread_bot_queues]

lemma tcb_sched_enqueue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace>
    tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_enqueue_valid_blocked_except_set_const:
  "tcb_sched_action tcb_sched_enqueue thread \<lbrace>valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_append_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace>
    tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_sched_append_valid_blocked_except_set_const:
  "tcb_sched_action tcb_sched_append thread \<lbrace>valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

(* tcb_sched_dequeue *)
lemma tcb_sched_dequeue_valid_blocked_except_set':
  "\<lbrace>\<lambda>s. valid_blocked_except_set S s \<and> t \<in> S\<rbrace>
    tcb_sched_action tcb_sched_dequeue t
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps valid_blocked_thread_def)

lemmas tcb_sched_dequeue_valid_blocked_except_set
  = tcb_sched_dequeue_valid_blocked_except_set'[where S="insert t S" and t=t for t S, simplified]

lemma tcb_sched_dequeue_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S and valid_blocked_thread_of Not id S t\<rbrace>
    tcb_sched_action tcb_sched_dequeue t
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps valid_blocked_thread_def)

lemma tcb_sched_dequeue_valid_blocked_except_set_remove: (* valid_sched is broken at thread *)
  "\<lbrace>valid_blocked_except_set (insert t S) and valid_blocked_thread_of \<bottom> id S t\<rbrace>
    tcb_sched_action tcb_sched_dequeue t
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_blocked_defs valid_sched_wpsimps in_queues_2_def)

(* Move *)
lemma if_fun_simp2: "(\<lambda>x1 x2. if x1 = y1 \<and> x2 = y2 then f y1 y2 else f x1 x2) = f "
  by (rule all_ext) auto

lemma tcb_sched_dequeue_not_queued_inv:
  "\<lbrace>P and not_queued thread\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp wp: thread_get_wp' set_tcb_queue_wp
              simp: tcb_sched_dequeue_def tcb_sched_action_def)
  apply (clarsimp simp: not_queued_def obj_at_def elim!: rsubst[where P=P])
  by (drule_tac x="tcb_domain tcb" and y="tcb_priority tcb" in spec2)
     (subst filter_True; clarsimp simp: if_fun_simp2)

lemma tcb_sched_dequeue_ready_or_release[wp]:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>\<lambda>s. ready_or_release s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: set_tcb_queue_wp)
  apply (clarsimp simp: tcb_sched_dequeue_def ready_or_release_2_def in_queues_2_def)
  by (fastforce)

lemma tcb_sched_enqueue_ready_or_release[wp]:
  "\<lbrace>ready_or_release and not_in_release_q t\<rbrace>
   tcb_sched_action tcb_sched_enqueue t
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: set_tcb_queue_wp)
  by (fastforce simp: tcb_sched_enqueue_def ready_or_release_2_def in_queues_2_def)

lemma tcb_sched_append_ready_or_release[wp]:
  "\<lbrace>ready_or_release and not_in_release_q t\<rbrace>
   tcb_sched_action tcb_sched_append t
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: set_tcb_queue_wp)
  by (fastforce simp: tcb_sched_append_def ready_or_release_2_def in_queues_2_def)

lemma tcb_sched_enqueue_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread
    and not_cur_thread thread
    and active_sc_tcb_at thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread and not_in_release_q thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: valid_sched_wp
              simp: valid_sched_wpsimps released_sc_tcb_at_def ready_or_release_2_def)
  by fast

lemma tcb_sched_enqueue_valid_sched_weak:
  "\<lbrace>valid_sched and st_tcb_at runnable thread
    and not_cur_thread thread
    and active_sc_tcb_at thread
    and budget_ready thread and budget_sufficient thread and not_in_release_q thread\<rbrace>
   tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: valid_sched_wp
              simp: valid_sched_wpsimps released_sc_tcb_at_def ready_or_release_2_def)
  by fast

lemma tcb_sched_append_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and active_sc_tcb_at thread
     and not_cur_thread thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread and not_in_release_q thread\<rbrace>
      tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: valid_sched_wp
              simp: valid_sched_wpsimps released_sc_tcb_at_def ready_or_release_2_def)
  by fast

lemma tcb_sched_dequeue_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps ready_or_release_2_def in_ready_q_def)
  by blast

lemma tcb_sched_enqueue_not_queued:
  "\<lbrace>not_queued t and K (thread \<noteq> t)\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

\<comment> \<open>tcb_release_remove\<close>

lemma tcb_release_remove_wp[valid_sched_wp]:
  "\<lbrace>\<lambda>s. P (release_queue_update (tcb_sched_dequeue thread) s)\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def obj_at_def)

lemma tcb_release_remove_valid_sched_misc[wp]:
  "tcb_release_remove t \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                               (ready_queues s) (scheduler_action s) (last_machine_time_of s)
                               (kheap s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma tcb_release_remove_valid_blocked_simp:
  assumes "T \<subseteq> S"
  assumes " valid_blocked_except_set_2 T queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes "valid_blocked_thread id Not S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs thread"
  shows "valid_blocked_except_set_2 S queues (tcb_sched_dequeue thread rlq) sa ct tcb_sts
                                      tcb_scps sc_refill_cfgs"
  using assms
  by (auto simp: valid_blocked_thread_def tcb_sched_dequeue_def in_queue_2_def
          elim!: valid_blockedE)

\<comment> \<open>Use more concrete T and S to avoid simplifier slow-down\<close>
lemmas tcb_release_remove_valid_blocked_simps[valid_sched_wpsimps] =
  tcb_release_remove_valid_blocked_simp[OF subset_refl]
  tcb_release_remove_valid_blocked_simp[where T=S and S="insert t' S" for t' S
                                        , OF subset_insertI, simplified]

lemmas tcb_release_remove_valid_blocked_bot_simps[valid_sched_wpsimps] =
  tcb_release_remove_valid_blocked_simps[OF _ valid_blocked_thread_bot_release_q]

lemma tcb_release_remove_weak_valid_sched_action_simp[valid_sched_wpsimps]:
  "weak_valid_sched_action_2 S curtime sa rlq tcb_sts tcb_scps sc_refill_cfgs
    \<Longrightarrow> weak_valid_sched_action_2 S curtime sa (tcb_sched_dequeue thread rlq) tcb_sts tcb_scps
                                  sc_refill_cfgs"
  by (simp add: weak_valid_sched_action_2_def tcb_sched_dequeue_def)

lemma tcb_release_remove_valid_sched_action_simp[valid_sched_wpsimps]:
  "valid_sched_action_2 wk S curtime sa ct cdom rlq etcb_heap tcb_sts tcb_scps sc_refill_cfgs
    \<Longrightarrow> valid_sched_action_2 wk S curtime sa ct cdom (tcb_sched_dequeue thread rlq) etcb_heap tcb_sts
                             tcb_scps sc_refill_cfgs"
  by (simp add: valid_sched_action_2_def valid_sched_wpsimps)

lemma tcb_release_remove_valid_blocked_except:
  "\<lbrace>valid_blocked_except thread\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps valid_blocked_thread_def)

lemma tcb_release_remove_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_release_remove_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma release_queue_update_idem:
  "f (release_queue s) = release_queue s \<Longrightarrow> release_queue_update f s = s"
  by auto

lemma tcb_release_remove_not_in_release_q_inv:
  "\<lbrace>P and not_in_release_q thread\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: not_in_release_q_def tcb_sched_dequeue_def filter_id_conv
          elim!: ssubst[OF release_queue_update_idem, rotated])

(* FIXME: move *)
lemma sorted_wrt_filter[elim!]:
  "sorted_wrt P xs \<Longrightarrow> sorted_wrt P (filter f xs)"
  by (induct xs) auto

lemma tcb_release_remove_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. sorted_release_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: tcb_sched_dequeue_def sorted_release_q_2_def)

lemma tcb_release_remove_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_release_q_def tcb_sched_dequeue_def sorted_release_q_2_def)

lemma tcb_release_remove_valid_blocked_except_set_incl:
  "\<lbrace>\<lambda>s. valid_blocked_except_set S s \<and> t \<in> S\<rbrace>
   tcb_release_remove t
   \<lbrace>\<lambda>rv s. valid_blocked_except_set S s\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto elim!: valid_blockedE' simp: valid_sched_wpsimps in_queue_2_def)

lemma tcb_release_remove_valid_blocked:
  "\<lbrace>valid_blocked_except_set S and valid_blocked_thread_of id Not S thread\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps valid_blocked_thread_def)

lemma tcb_release_remove_valid_blocked_remove: (* valid_sched is broken at thread *)
  "\<lbrace>valid_blocked_except_set (insert thread S) and valid_blocked_thread_of id \<bottom> S thread\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_blocked_defs valid_sched_wpsimps in_queue_2_def tcb_sched_dequeue_def)

\<comment> \<open>set_scheduler_action\<close>

lemma set_scheduler_action_wp[valid_sched_wp]:
  "\<lbrace>\<lambda>s. Q (scheduler_action_update (\<lambda>_. a) s)\<rbrace> set_scheduler_action a \<lbrace>\<lambda>_.Q\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma set_scheduler_action_valid_sched_misc[wp]:
  "set_scheduler_action a \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                                 (idle_thread s) (ready_queues s) (release_queue s) (last_machine_time_of s)
                                 (kheap s)\<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma simple_sched_action_def2[valid_sched_wpsimps]:
  "simple_sched_action_2 action \<equiv> action = resume_cur_thread \<or> action = choose_new_thread"
  by (auto simp: atomize_eq simple_sched_action_2_def split: scheduler_action.splits)

lemmas [valid_sched_wpsimps] =
  ct_not_in_q_def is_activatable_def valid_sched_action_def ct_in_cur_domain_def

lemma set_scheduler_action_rct_ct_not_in_q:
  "\<lbrace>ct_not_queued\<rbrace> set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_scheduler_action_rct_is_activatable:
  "\<lbrace>st_tcb_at activatable t\<rbrace>
     set_scheduler_action resume_cur_thread
   \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_scheduler_action_rct_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_rct_valid_sched_action:
  "\<lbrace>\<lambda>s. st_tcb_at activatable (cur_thread s) s\<rbrace>
     set_scheduler_action resume_cur_thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_scheduler_action_rct_ct_in_cur_domain:
  "\<lbrace>\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s\<rbrace>
     set_scheduler_action resume_cur_thread  \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_scheduler_action_valid_blocked_simple:
  "\<lbrace>valid_blocked_except_set S and simple_sched_action and (K (simple_sched_action_2 schact)) \<rbrace>
   set_scheduler_action schact
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_valid_blocked: (* when the next one doesn't hold *)
  "\<lbrace>valid_blocked_except_set S and (\<lambda>s. scheduler_action s = switch_thread t) \<rbrace>
     set_scheduler_action act
   \<lbrace>\<lambda>_. valid_blocked_except_set (insert t S)\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_valid_blocked_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
                t \<in> S \<or> in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
                  \<or> \<not> (st_tcb_at active t s \<and> active_sc_tcb_at t s)) \<rbrace>
     set_scheduler_action act
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_valid_blocked_remove:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert t S) (s\<lparr>scheduler_action := switch_thread t\<rparr>)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_rct_valid_sched_simple:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and simple_sched_action\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_rct_valid_sched_ct:
  "\<lbrace>valid_sched and ct_not_queued and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_cnt_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_scheduler_action_cnt_is_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_is_activatable'[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>r s. is_activatable (t s) s\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_switch_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_scheduler_action_cnt_weak_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto elim!: valid_blockedE' simp: valid_sched_wpsimps)

lemma set_scheduler_action_simple_sched_action:
  "\<lbrace>K $ simple_sched_action_2 action\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemmas [valid_sched_wpsimps] = not_cur_thread_def

lemma set_sched_action_cnt_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_sched_action_st_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action (switch_thread thread) \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

\<comment> \<open>schedule_tcb\<close>

(* FIXME RT: simplify the spec for schedule_tcb? *)
lemma reschedule_required_resume_cur_thread_choose_new_thread_rewrite:
  "monadic_rewrite False True (\<lambda>s. scheduler_action s = resume_cur_thread)
                   reschedule_required (set_scheduler_action choose_new_thread)"
  apply (simp add: reschedule_required_def)
  apply (rule monadic_rewrite_trans[where Q=\<top>, OF monadic_rewrite_gets_known[where rv=resume_cur_thread], simplified])
  by (simp add: monadic_rewrite_refl)

(* FIXME RT: simplify the spec for schedule_tcb? *)
lemma schedule_tcb_choose_new_thread_rewrite:
  "monadic_rewrite False True \<top> (schedule_tcb t)
                   (do cur \<leftarrow> gets cur_thread;
                       sched_act \<leftarrow> gets scheduler_action;
                       in_release_q \<leftarrow> gets $ in_release_q t;
                       schedulable \<leftarrow> is_schedulable t in_release_q;
                       when (t = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable)
                         $ set_scheduler_action choose_new_thread
                     od)"
  apply (fold in_release_queue_in_release_q)
  apply (simp add: schedule_tcb_def)
  apply (rule monadic_rewrite_bind_tail[OF _ gets_inv])
  apply (rule monadic_rewrite_bind_tail[OF _ hoare_gets_sp], simp)
  apply (rule monadic_rewrite_bind_tail[OF _ gets_inv])
  apply (rule monadic_rewrite_bind_tail[OF _ is_schedulable_inv])
  apply (simp add: when_def split del: if_split)
  apply (rule monadic_rewrite_imp[OF monadic_rewrite_if])
    apply (rule reschedule_required_resume_cur_thread_choose_new_thread_rewrite)
   apply (rule monadic_rewrite_refl)
  by simp

lemmas schedule_tcb_def2 = monadic_rewrite_to_eq[OF schedule_tcb_choose_new_thread_rewrite]

(* FIXME RT: move near is_schedulable_wp *)
lemma is_schedulable_wp':
  "\<lbrace>\<lambda>s. P (pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s \<and> \<not> in_q) s\<rbrace>
   is_schedulable t in_q
   \<lbrace>P\<rbrace>"
  by (wpsimp wp: is_schedulable_wp) (auto simp: obj_at_kh_kheap_simps is_schedulable_bool_def2)

lemma schedule_tcb_wp:
  "\<lbrace>\<lambda>s. if t = cur_thread s \<and> scheduler_action s = resume_cur_thread
            \<and> (pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s \<longrightarrow> in_release_q t s)
        then P (s\<lparr>scheduler_action := choose_new_thread\<rparr>) else P s\<rbrace>
   schedule_tcb t
   \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: schedule_tcb_def2 wp: set_scheduler_action_wp is_schedulable_wp')

lemma schedule_tcb_valid_sched_misc[wp]:
  "schedule_tcb t \<lbrace>\<lambda>s. P (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                         (ready_queues s) (release_queue s) (last_machine_time_of s)
                         (kheap s)\<rbrace>"
  by (wpsimp wp: schedule_tcb_wp)

lemma schedule_tcb_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. P (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
          (if t = cur_thread s \<and> scheduler_action s = resume_cur_thread
              \<and> (pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s \<longrightarrow> in_release_q t s)
           then choose_new_thread else (scheduler_action s))
          (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
          (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   schedule_tcb t
   \<lbrace>\<lambda>_. valid_sched_pred P\<rbrace>"
  by (wpsimp wp: schedule_tcb_wp split: if_splits)

(* FIXME: move up *)
lemma not_cur_thread_2_simps[simp]:
  "not_cur_thread_2 t choose_new_thread ct"
  "not_cur_thread_2 t (switch_thread t') ct"
  "t \<noteq> ct \<Longrightarrow> not_cur_thread_2 t sa ct"
  by (auto simp: not_cur_thread_2_def)

(* FIXME: move up *)
lemma ct_not_in_q_2_simps[simp]:
  "ct_not_in_q_2 qs choose_new_thread ct"
  "ct_not_in_q_2 qs (switch_thread t) ct"
  "not_queued_2 qs ct \<Longrightarrow> ct_not_in_q_2 qs sa ct"
  by (auto simp: ct_not_in_q_2_def)

lemma schedule_tcb_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> schedule_tcb ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

\<comment> \<open>reschedule_required\<close>

abbreviation (input) reschedule_required_wp where
  "reschedule_required_wp P s \<equiv>
    if \<forall>t. scheduler_action s = switch_thread t
            \<and> pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s
           \<longrightarrow> in_release_q t s
    then P (s\<lparr>scheduler_action := choose_new_thread\<rparr>)
    else \<forall>t p d. scheduler_action s = switch_thread t
                  \<and> etcb_eq p d t s \<and> budget_ready t s \<and> budget_sufficient t s
                 \<longrightarrow> P (ready_queues_update (tcb_sched_ready_q_update d p (tcb_sched_enqueue t)) s
                         \<lparr>scheduler_action := choose_new_thread\<rparr>)"

lemma reschedule_required_wp[valid_sched_wp]:
  "\<lbrace>reschedule_required_wp P\<rbrace> reschedule_required \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: reschedule_required_def
                  wp: set_scheduler_action_wp tcb_sched_action_wp thread_get_wp' is_schedulable_wp')
  by (auto simp: vs_all_heap_simps obj_at_kh_kheap_simps)

lemma reschedule_required_valid_sched_misc[wp]:
  "reschedule_required \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                              (idle_thread s) (release_queue s) (last_machine_time_of s) (kheap s)\<rbrace>"
  by (wpsimp wp: reschedule_required_wp)

lemma reschedule_required_ready_or_release[wp]:
  "reschedule_required \<lbrace>ready_or_release\<rbrace>"
  unfolding reschedule_required_def
  apply (wpsimp wp: thread_get_wp is_schedulable_wp)
  by (clarsimp simp: obj_at_def is_schedulable_bool_def split: option.splits dest!: get_tcb_SomeD)

lemma reschedule_required_valid_ready_qs[wp]:
  "reschedule_required \<lbrace>valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps released_sc_tcb_at_def)

lemma reschedule_required_lift:
  assumes A: "\<And>t. \<lbrace>P\<rbrace> tcb_sched_action (tcb_sched_enqueue) t \<lbrace>\<lambda>_. P\<rbrace>"
  assumes B: "\<lbrace>P\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> reschedule_required \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding reschedule_required_def
  by (wpsimp wp: A B is_schedulable_wp' thread_get_wp')

lemma reschedule_required_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_is_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_scheduler_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma reschedule_required_valid_blocked:
  "reschedule_required \<lbrace>valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (auto elim!: valid_blockedE' simp: valid_sched_wpsimps runnable_eq_active)

lemma reschedule_required_valid_sched_except_blocked:
  "\<lbrace>valid_release_q and valid_ready_qs
                    and ready_or_release
                    and weak_valid_sched_action
                    and valid_idle_etcb
                    and released_ipc_queues
                    and active_reply_scs
                    and valid_machine_time
                    and active_sc_valid_refills\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_sched_wpsimps released_sc_tcb_at_def runnable_eq_active
                 ready_or_release_2_def
          elim!: valid_blockedE')

lemma reschedule_required_valid_sched':
  "\<lbrace>valid_release_q and valid_ready_qs
                    and ready_or_release
                    and valid_blocked
                    and valid_idle_etcb
                    and released_ipc_queues
                    and active_reply_scs
                    and valid_machine_time
                    and active_sc_valid_refills\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: reschedule_required_valid_blocked)

lemma reschedule_required_switch_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. not_cur_thread t\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma switch_thread_weak_valid_sched_action_is_schedulable:
  "\<lbrakk>scheduler_action s = switch_thread t; weak_valid_sched_action s; x = in_release_q t s\<rbrakk>
      \<Longrightarrow> the (is_schedulable_opt t x s)"
  by (auto simp: is_schedulable_opt_def in_queue_2_def weak_valid_sched_action_def
                 obj_at_kh_kheap_simps vs_all_heap_simps
          split: option.splits)

lemma switch_thread_valid_sched_is_schedulable:
  "\<lbrakk>scheduler_action s = switch_thread t; valid_sched s; x = in_release_q t s\<rbrakk>
      \<Longrightarrow> the (is_schedulable_opt t x s)"
  by (intro switch_thread_weak_valid_sched_action_is_schedulable
            valid_sched_weak_valid_sched_action)

lemma reschedule_valid_sched_except_blocked_const:
  "reschedule_required \<lbrace>valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: reschedule_required_valid_sched_except_blocked)
  by (simp add: valid_sched_def valid_sched_action_def)

lemma reschedule_valid_sched_const:
  "reschedule_required \<lbrace>valid_sched\<rbrace>"
  apply (wpsimp wp: reschedule_required_valid_sched')
  by (simp add: valid_sched_def valid_sched_action_def)

lemma reschedule_required_simple_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required  \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

crunch etcb_at[wp]: reschedule_required "etcb_at P t"

lemma reschedule_required_not_queued:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps scheduler_act_not_def)

lemma reschedule_required_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps scheduler_act_not_def)

lemma reschedule_required_scheduler_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

\<comment> \<open>test_reschedule\<close>

lemma test_reschedule_wp[valid_sched_wp]:
  "\<lbrace>\<lambda>s. if scheduler_action s \<noteq> switch_thread t \<and> cur_thread s \<noteq> t
        then P s
        else if \<forall>t. scheduler_action s = switch_thread t
                     \<and> pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s
                    \<longrightarrow> in_release_q t s
        then P (s\<lparr>scheduler_action := choose_new_thread\<rparr>)
        else \<forall>t p d. scheduler_action s = switch_thread t
                      \<and> etcb_eq p d t s \<and> budget_ready t s \<and> budget_sufficient t s
                     \<longrightarrow> P (ready_queues_update (tcb_sched_ready_q_update d p (tcb_sched_enqueue t)) s
                             \<lparr>scheduler_action := choose_new_thread\<rparr>)\<rbrace>
   test_reschedule t
   \<lbrace>\<lambda>rv. P\<rbrace>"
  supply if_split[split del]
  apply (wpsimp simp: test_reschedule_def wp: reschedule_required_wp)
  apply (clarsimp simp: if_distribR if_swap[where P="_ \<or> _"] elim!: if_weak_cong[THEN iffD1, rotated])
  by (auto split: scheduler_action.splits)

lemma test_reschedule_valid_sched_misc[wp]:
  "test_reschedule t \<lbrace>\<lambda>s. P (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                            (release_queue s) (last_machine_time_of s) (kheap s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma test_reschedule_valid_sched_action:
  "test_reschedule t \<lbrace>valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

\<comment> \<open>set_thread_state\<close>

definition
  set_thread_state_only :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_thread_state_only ref ts \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_state := ts \<rparr>))
   od"

lemma set_thread_state_def2:
  "set_thread_state ref ts \<equiv> do
     set_thread_state_only ref ts;
     set_thread_state_act ref
   od"
  by (simp add: set_thread_state_def set_thread_state_only_def bind_assoc)

crunches set_thread_state_act
  for valid_sched_except_sched_act[wp]:
    "\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
           (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
           (last_machine_time_of s) (kheap s)"

lemma set_thread_state_only_valid_sched_except_tcb_st[wp]:
  "set_thread_state_only t st
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
          (scheduler_action s) (last_machine_time_of s) (etcbs_of s) (tcb_scps_of s)
          (tcb_faults_of s) (scs_of s)\<rbrace>"
  by (wpsimp simp: set_thread_state_only_def vs_all_heap_simps obj_at_kh_kheap_simps sc_heap.all_simps
               wp: gets_the_wp' set_object_wp)

lemma set_thread_state_valid_sched_misc[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                                (cur_time s) (cur_domain s)
                                (cur_thread s) (idle_thread s)
                                (ready_queues s) (release_queue s)
                                (last_machine_time_of s) (etcbs_of s)
                                (tcb_scps_of s) (tcb_faults_of s) (scs_of s)\<rbrace>"
  by (wpsimp simp: set_thread_state_def2)

lemma set_thread_state_act_wp[valid_sched_wp]:
  "\<lbrace>\<lambda>s. if t = cur_thread s
           \<and> scheduler_action s = resume_cur_thread
           \<and> (pred_map runnable (tcb_sts_of s) t \<longrightarrow> active_sc_tcb_at t s \<longrightarrow> in_release_q t s)
        then P (s\<lparr>scheduler_action := choose_new_thread\<rparr>) else P s\<rbrace>
   set_thread_state_act t
   \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def wp: set_scheduler_action_wp is_schedulable_wp')

lemma set_thread_state_only_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. kheap s t = Some (TCB tcb)
              \<longrightarrow> P (kheap_update (\<lambda>kh. kh(t \<mapsto> TCB (tcb\<lparr>tcb_state := st\<rparr>))) s)\<rbrace>
   set_thread_state_only t st
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: set_thread_state_only_def fun_upd_def wp: set_object_wp, rename_tac tcb)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps elim!: rsubst[of P])

lemma set_thread_state_only_tcb_st_heap:
  "\<lbrace>\<lambda>s. pred_map \<top> (tcbs_of s) t \<longrightarrow>
        P (tcb_sts_of s(t \<mapsto> st))
          (tcb_scps_of s) (tcb_faults_of s) (scs_of s)
          (cur_thread s) (scheduler_action s) (release_queue s)\<rbrace>
   set_thread_state_only t st
   \<lbrace>\<lambda>rv s. P (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (scs_of s)
             (cur_thread s) (scheduler_action s) (release_queue s)\<rbrace>"
  by (wpsimp wp: set_thread_state_only_wp simp: fun_upd_def vs_all_heap_simps sc_heap.all_simps)

lemma set_thread_state_scheduler_action_tcb_st_heap:
  "\<lbrace>\<lambda>s. pred_map \<top> (tcbs_of s) t \<longrightarrow>
        P (tcb_sts_of s(t \<mapsto> st))
          (if t = cur_thread s
              \<and> scheduler_action s = resume_cur_thread
              \<and> (runnable st \<longrightarrow> active_sc_tcb_at t s \<longrightarrow> in_release_q t s)
           then choose_new_thread else scheduler_action s)
          (cur_thread s) (release_queue s) (tcb_scps_of s) (tcb_faults_of s) (scs_of s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv s. P (tcb_sts_of s) (scheduler_action s) (cur_thread s) (release_queue s)
             (tcb_scps_of s) (tcb_faults_of s) (scs_of s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def2 wp: set_thread_state_act_wp set_thread_state_only_tcb_st_heap)
  by (auto simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)

lemma set_thread_state_valid_sched_pred_strong':
  "\<lbrace>\<lambda>s. pred_map \<top> (tcbs_of s) t \<longrightarrow>
        P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s)
          (if t = cur_thread s
              \<and> scheduler_action s = resume_cur_thread
              \<and> (runnable st \<longrightarrow> active_sc_tcb_at t s \<longrightarrow> in_release_q t s)
           then choose_new_thread else scheduler_action s)
          (last_machine_time_of s) (etcbs_of s)
          (tcb_sts_of s(t \<mapsto> st))
          (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  apply (rule hoare_lift_Pf2[where f=consumed_time, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=cur_sc, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=ep_send_qs_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=ep_recv_qs_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=cur_time, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=cur_domain, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=idle_thread, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=ready_queues, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=last_machine_time_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf2[where f=etcbs_of, rotated], wpsimp)
  by (rule set_thread_state_scheduler_action_tcb_st_heap)

lemmas set_thread_state_valid_sched_pred_strong[valid_sched_wp]
  = set_thread_state_valid_sched_pred_strong'[THEN hoare_drop_assertion]

lemmas set_thread_state_valid_sched_pred
  = set_thread_state_valid_sched_pred_strong[where P="\<lambda>_ _ _ _ _. P :: valid_sched_t" for P]

lemma set_thread_state_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. \<not> runnable ts \<longrightarrow> not_queued thread s)\<rbrace>
   set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_ready_qs_def vs_all_heap_simps not_queued_def, fastforce)

lemma set_thread_state_valid_release_q:
  "\<lbrace>valid_release_q
    and (\<lambda>s. \<not> runnable ts \<longrightarrow> not_in_release_q ref s)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_release_q_def vs_all_heap_simps in_release_q_def)

lemma set_thread_state_act_ct_not_in_q:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state_act ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_thread_state_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma set_thread_state_act_is_activatable:
  "\<lbrace>\<lambda>s. ref \<noteq> cur_thread s \<longrightarrow> is_activatable (cur_thread s) s\<rbrace>
     set_thread_state_act ref
   \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: is_activatable_def vs_all_heap_simps)

lemma set_thread_state_cur_is_activatable:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: is_activatable_def vs_all_heap_simps)

lemma set_thread_state_act_weak_valid_sched_action:
  "set_thread_state_act ref \<lbrace>weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_thread_state_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. \<not> runnable ts \<longrightarrow> scheduler_act_not ref s)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: weak_valid_sched_action_def vs_all_heap_simps scheduler_act_not_def)

lemma set_thread_state_switch_in_cur_domain:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma set_thread_state_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. \<not> runnable ts \<longrightarrow> scheduler_act_not ref s)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp
           simp: valid_sched_wpsimps weak_valid_sched_action_def vs_all_heap_simps scheduler_act_not_def, fastforce)

lemma set_thread_state_cur_ct_in_cur_domain[wp]:
  "set_thread_state ref ts \<lbrace>ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

(* FIXME: move *)
lemma set_thread_state_ep_at_ppred[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. N (ep_at_ppred proj P p s)\<rbrace>"
  by (wpsimp simp: ep_at_ppred_def wp: sts_obj_at_impossible')

(* FIXME: move *)
lemma set_thread_state_ntfn_at_ppred[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. N (ntfn_at_ppred proj P p s)\<rbrace>"
  by (wpsimp simp: ntfn_at_ppred_def wp: sts_obj_at_impossible')

(* FIXME: replace existibg sts_obj_at_impossible'? *)
lemma sts_obj_at_impossible'':
  assumes "\<And>tcb st. P (TCB tcb) \<Longrightarrow> P (TCB (tcb\<lparr>tcb_state := st\<rparr>))"
  shows "set_thread_state t st \<lbrace>\<lambda>s. N (obj_at P p s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def wp: set_object_wp)
  apply (rename_tac tcb)
  apply (clarsimp elim!: rsubst[of N] dest!: get_tcb_SomeD simp: obj_at_def)
  apply (rule iffI, erule assms)
  apply (drule_tac st="tcb_state tcb" in assms, simp)
  done

lemma set_thread_state_runnable_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and (\<lambda>s. runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_ready_qs
                    set_thread_state_valid_release_q
                    set_thread_state_ct_not_in_q
                    set_thread_state_valid_sched_action
                    set_thread_state_cur_ct_in_cur_domain
                    set_thread_state_valid_sched_pred[where P=valid_sched_ipc_queues]
                    valid_idle_etcb_lift
              simp: valid_sched_def)
  by (auto simp: fun_upd_def vs_all_heap_simps is_blocked_thread_state_defs runnable_eq_active
          split: if_splits
          elim!: released_ipc_queuesE)

lemma set_thread_state_act_valid_blocked:
  "set_thread_state_act ref \<lbrace>valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto simp: valid_sched_wpsimps elim: valid_blockedE')

(* This is very close to a true weakest precondition statement *)
lemma set_thread_state_valid_blocked:
  "\<lbrace>valid_blocked_except_set (insert t S) and
      (\<lambda>s. runnable ts \<longrightarrow> active_sc_tcb_at t s
           \<longrightarrow> (t \<in> S \<or> in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
               \<or> scheduler_action s = switch_thread t)) \<rbrace>
   set_thread_state t ts
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (intro conjI impI; clarsimp simp: vs_all_heap_simps valid_blocked_defs split: if_splits)
  by auto

(* FIXME RT: remove, use set_thread_state_valid_blocked instead. *)
lemma set_thread_state_valid_blocked_const:
  "\<lbrace>valid_blocked_except_set S and
      (\<lambda>s. t \<in> S \<or> in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
                  \<or> scheduler_action s = switch_thread t
                  \<or> (runnable ts \<longrightarrow> \<not> active_sc_tcb_at t s)) \<rbrace>
      set_thread_state t ts
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: set_thread_state_valid_blocked)

(* FIXME RT: remove, use set_thread_state_valid_blocked instead. *)
lemma set_thread_state_not_runnable_valid_blocked_remove:
  "\<lbrace>valid_blocked_except_set (insert ref S) and K (\<not> runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. (valid_blocked_except_set S)\<rbrace>"
  by (wpsimp wp: set_thread_state_valid_blocked)

lemma set_thread_state_active_valid_sched:
  "active st \<Longrightarrow>
   \<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct st \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp simp: valid_sched_def runnable_eq ct_in_state_def runnable_eq_active
                  wp: set_thread_state_valid_sched_action
                      set_thread_state_valid_blocked
                      set_thread_state_valid_ready_qs
                      set_thread_state_valid_release_q
                      set_thread_state_ct_not_in_q
                      set_thread_state_cur_ct_in_cur_domain
                      set_thread_state_valid_sched_pred[where P=valid_sched_ipc_queues])
  by (auto simp: vs_all_heap_simps fun_upd_def is_blocked_thread_state_defs
          elim!: released_ipc_queuesE split: if_splits)

lemma set_thread_state_Running_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct Running \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule set_thread_state_active_valid_sched) simp

lemma set_thread_state_Restart_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
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
  apply (wpsimp wp: set_thread_state_valid_ready_qs)
  apply (simp add: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (simp add: valid_ready_qs_def in_ready_q_def)
  by (fastforce simp: vs_all_heap_simps)

lemma set_thread_state_not_runnable_valid_release_q:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> pred_map (\<lambda>ts. \<not> runnable ts) (tcb_sts_of s) ref\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_thread_state_act_def wp: set_object_wp, rename_tac tcb)
  apply (simp add: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (simp add: valid_release_q_def, elim conjE ballEI)
  by (clarsimp simp add: vs_all_heap_simps)

lemma set_thread_state_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> (in_ready_q t s \<or> in_release_q t s \<or> scheduler_action s = switch_thread t \<longrightarrow> runnable st)
         \<and> (is_blocked_on_recv_ntfn st \<longrightarrow> released_if_bound_sc_tcb_at t s)
         \<and> (is_blocked_on_send st \<longrightarrow> valid_sender_sc_tcb_at t s)
         \<and> (is_blocked_on_reply st \<longrightarrow> active_if_bound_sc_tcb_at t s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: valid_sched_wp simp: valid_sched_def split_del: if_split)
  apply (intro conjI)
       apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps in_queues_2_def)
      apply (clarsimp simp: valid_release_q_def vs_all_heap_simps in_queue_2_def)
     apply clarsimp
    apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def is_activatable_def
                          vs_all_heap_simps)
   apply clarsimp
  by (clarsimp simp: vs_all_heap_simps is_blocked_thread_state_defs
              elim!: released_ipc_queuesE)

lemma set_thread_state_not_runnable_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> \<not> pred_map runnable (tcb_sts_of s) t
         \<and> (is_blocked_on_recv_ntfn st \<longrightarrow> released_if_bound_sc_tcb_at t s)
         \<and> (is_blocked_on_send st \<longrightarrow> valid_sender_sc_tcb_at t s)
         \<and> (is_blocked_on_reply st \<longrightarrow> active_if_bound_sc_tcb_at t s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_sched_except_blocked simp: valid_sched_def)
  apply (intro conjI; clarsimp)
    apply (fastforce simp: valid_ready_qs_def in_queues_2_def vs_all_heap_simps)
   apply (fastforce simp: valid_release_q_def in_queue_2_def vs_all_heap_simps)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def)
  done

(* FIXME RT: see if it's possible to use set_thread_state_valid_sched_except_blocked instead. *)
lemmas set_thread_state_Inactive_not_runnable_valid_sched_except_blocked
  = set_thread_state_not_runnable_valid_sched_except_blocked[where st=Inactive, simplified]

lemma set_thread_state_Inactive_not_queued_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> valid_blocked_except ref s
        \<and> scheduler_act_not ref s \<and> not_queued ref s \<and> not_in_release_q ref s\<rbrace>
   set_thread_state ref Inactive
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: set_thread_state_valid_sched_except_blocked
                 set_thread_state_valid_blocked
           simp: valid_sched_valid_sched_except_blocked scheduler_act_not_def)

lemma set_thread_state_Inactive_not_runnable_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> valid_blocked_except ref s
        \<and> \<not> pred_map runnable (tcb_sts_of s) ref\<rbrace>
   set_thread_state ref Inactive
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: set_thread_state_Inactive_not_runnable_valid_sched_except_blocked
                 set_thread_state_valid_blocked
           simp: valid_sched_valid_sched_except_blocked)

crunch simple_sched_action[wp]: set_thread_state_act,schedule_tcb simple_sched_action
  (wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma set_thread_state_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_thread_state param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

crunch not_cur_thread[wp]: schedule_tcb "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2 reschedule_required_wp)

lemma set_thread_state_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread thread\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv. not_cur_thread thread\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

(* FIXME: move *)
lemma if_cancel_eq_True:
  "(c \<Longrightarrow> x = y) \<Longrightarrow> (if c then x else y) = y"
  by simp

(* FIXME: move *)
lemma if_cancel_eq_False:
  "(\<not>c \<Longrightarrow> x = y) \<Longrightarrow> (if c then x else y) = x"
  by auto

(* FIXME: move *)
lemmas if_cancel_eq_assm =
  if_cancel_eq_True if_cancel_eq_False

lemma set_thread_state_valid_release_q_except:
  "\<lbrace>valid_release_q\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_release_q_except thread\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_release_q_def vs_all_heap_simps)

lemma tcb_release_remove_valid_release_q_except:
  "\<lbrace>valid_release_q_except thread\<rbrace>
      tcb_release_remove thread
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_release_q_def tcb_sched_dequeue_def sorted_release_q_def)

lemma set_thread_state_Inactive_simple_sched_action_not_runnable:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> valid_blocked_except thread s
        \<and> simple_sched_action s \<and> \<not> pred_map runnable (tcb_sts_of s) thread\<rbrace>
   set_thread_state thread Inactive
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp wp: set_thread_state_Inactive_not_runnable_valid_sched)

global_interpretation schedule_tcb: non_heap_op "schedule_tcb t"
  by unfold_locales (wpsimp wp: schedule_tcb_wp)

crunches schedule_tcb
  for ct_active[wp]: ct_active

lemmas set_thread_state_active_valid_sched_except_blocked =
  set_thread_state_runnable_valid_sched_except_blocked[simplified runnable_eq_active]

lemma set_thread_state_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
         \<and> (is_blocked_on_recv_ntfn ts \<longrightarrow> released_if_bound_sc_tcb_at ref s)
         \<and> (is_blocked_on_send ts \<longrightarrow> valid_sender_sc_tcb_at ref s)
         \<and> (is_blocked_on_reply ts \<longrightarrow> active_if_bound_sc_tcb_at ref s)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (erule released_ipc_queuesE)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps runnable_eq)

lemma set_thread_state_runnable_released_ipc_queues:
  "\<lbrace>released_ipc_queues and (\<lambda>s. runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  apply (wpsimp wp: set_thread_state_released_ipc_queues)
  by (case_tac ts; simp)

lemma set_thread_state_runnable_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_ready_qs set_thread_state_valid_blocked_const
                    set_thread_state_valid_sched_action set_thread_state_runnable_released_ipc_queues
                    set_thread_state_valid_release_q simp: valid_sched_def)
  by (auto simp: valid_blocked_defs runnable_eq_active obj_at_kh_kheap_simps)

lemma set_thread_state_break_valid_sched:  (* ref is previously blocked *)
  "\<lbrace>valid_sched and K (runnable ts)\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_except_blocked and valid_blocked_except ref\<rbrace>"
  apply (wpsimp wp: set_thread_state_runnable_valid_sched_except_blocked
                    set_thread_state_valid_blocked_const)
  apply (clarsimp simp: valid_sched_def)
  done

crunch ct_sched_act_not[wp]: set_thread_state "\<lambda>s. scheduler_act_not (cur_thread s) s"
  (wp: set_scheduler_action_wp gts_wp hoare_drop_imp
   simp: crunch_simps
   ignore: set_scheduler_action)

(* FIXME: move to KHeap_AI *)
lemma set_tcb_obj_ref_pred_tcb_at:
  assumes "\<And>tcb. proj (tcb_to_itcb (f (\<lambda>_. v) tcb)) = proj (tcb_to_itcb tcb)"
  shows "set_tcb_obj_ref f ref v \<lbrace>\<lambda>s. N (pred_tcb_at proj P t s)\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: pred_tcb_at_def obj_at_def assms)

lemma set_tcb_obj_ref_sc_at_pred_n[wp]:
  "set_tcb_obj_ref f ref v \<lbrace>\<lambda>s. R (sc_at_pred_n N proj P p s)\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: sc_at_pred_n_def obj_at_def)

lemma set_tcb_obj_ref_is_sc_active[wp]:
  "set_tcb_obj_ref f ref tptr \<lbrace>\<lambda>s. P (is_sc_active scp s)\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma set_tcb_obj_ref_is_refill_ready[wp]:
  "set_tcb_obj_ref f ref tptr \<lbrace>is_refill_ready scp\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma set_tcb_obj_ref_valid_sched_except_tcb_heap[wp]:
  "set_tcb_obj_ref f ref v \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                                  (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                                  (ready_queues s) (release_queue s) (scheduler_action s)
                                  (last_machine_time_of s) (scs_of s)\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp
           simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps sc_heap.all_simps)

lemma set_tcb_obj_ref_valid_sched_except_tcb_scp_heap:
  assumes "\<And>tcb. tcb_state (f (\<lambda>_. v) tcb) = tcb_state tcb"
  assumes "\<And>tcb. tcb_fault (f (\<lambda>_. v) tcb) = tcb_fault tcb"
  assumes "\<And>tcb. etcb_of (f (\<lambda>_. v) tcb) = etcb_of tcb"
  shows "set_tcb_obj_ref f ref v \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s)
                                        (ep_recv_qs_of s) (sc_tcbs_of s) (sc_replies_of s)
                                        (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                                        (ready_queues s) (release_queue s) (scheduler_action s)
                                        (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
                                        (tcb_faults_of s) (scs_of s)\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp
           simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps sc_heap.all_simps assms)

lemma set_tcb_obj_ref_valid_sched_pred:
  assumes "\<And>tcb. tcb_state (f (\<lambda>_. v) tcb) = tcb_state tcb"
  assumes "\<And>tcb. tcb_sched_context (f (\<lambda>_. v) tcb) = tcb_sched_context tcb"
  assumes "\<And>tcb. tcb_fault (f (\<lambda>_. v) tcb) = tcb_fault tcb"
  assumes "\<And>tcb. etcb_of (f (\<lambda>_. v) tcb) = etcb_of tcb"
  shows "set_tcb_obj_ref f ref v \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps assms)

lemmas set_bound_notification_valid_sched_pred[wp] =
  set_tcb_obj_ref_valid_sched_pred[where f=tcb_bound_notification_update, simplified]

lemmas set_tcb_yield_to_valid_ready_qs[wp] =
  set_tcb_obj_ref_valid_sched_pred[where f=tcb_yield_to_update, simplified]

lemmas set_tcb_sched_context_valid_sched_except_tcb_scp_heap[wp] =
  set_tcb_obj_ref_valid_sched_except_tcb_scp_heap[where f=tcb_sched_context_update, simplified]

lemma set_tcb_sched_context_valid_sched_pred':
  "\<lbrace>\<lambda>s. pred_map \<top> (tcb_sts_of s) ref
        \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
              (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
              (scheduler_action s) (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
              (tcb_scps_of s(ref \<mapsto> scpo)) (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref scpo
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps)

\<comment> \<open>The implication in the set_tcb_sched_context_valid_sched_pred' precondition
    is probably not useful, but this is to document that we are throwing away some
    information.\<close>
lemmas set_tcb_sched_context_valid_sched_pred[valid_sched_wp] =
  set_tcb_sched_context_valid_sched_pred'[THEN hoare_drop_assertion]

lemma set_tcb_sched_context_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and not_queued ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref sc
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_ready_qs_def vs_all_heap_simps not_queued_def)

lemma set_tcb_sched_context_None_released_ipc_queues:
  "\<lbrace>released_ipc_queues\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref None
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: released_ipc_queues_defs vs_all_heap_simps not_queued_def)

lemma set_tcb_sched_context_None_valid_blocked:
  "\<lbrace>valid_blocked_except ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref None
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp wp: valid_sched_wp simp: valid_blocked_defs vs_all_heap_simps)
  by auto

lemma valid_ready_qs_no_sc_not_queued:
  "\<lbrakk>valid_ready_qs s; pred_map_eq None (tcb_scps_of s) ref\<rbrakk> \<Longrightarrow> not_queued ref s"
  by (fastforce simp: valid_ready_qs_def in_ready_q_def vs_all_heap_simps)

lemma set_tcb_sched_context_valid_ready_qs_no_sc:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> pred_map_eq None (tcb_scps_of s) ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref sc
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
           simp: valid_ready_qs_no_sc_not_queued)

lemma set_tcb_sched_context_valid_release_q_not_queued:
  "\<lbrace>valid_release_q and not_in_release_q ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref sc
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_wp simp: valid_release_q_def vs_all_heap_simps not_in_release_q_def)
  apply (clarsimp elim!: sorted_release_qE simp: sc_ready_time_eq_iff)
  by (clarsimp simp: tcb_ready_times_defs map_project_simps opt_map_simps map_join_simps)

lemma valid_release_q_no_sc_not_in_release_q:
  "\<lbrakk>valid_release_q s; pred_map_eq None (tcb_scps_of s) ref\<rbrakk> \<Longrightarrow> not_in_release_q ref s"
  by (auto simp: valid_release_q_def in_release_q_def vs_all_heap_simps)

lemma set_tcb_sched_context_valid_release_q_no_sc:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> pred_map_eq None (tcb_scps_of s) ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref sc
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_release_q_not_queued
           simp: valid_release_q_no_sc_not_in_release_q)

lemma set_tcb_sched_context_valid_ready_qs_Some: (* when ref is in ready_queeus *)
  "\<lbrace>\<lambda>s. valid_ready_qs s
        \<and> (in_ready_q ref s \<longrightarrow> released_sc_at sp s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref (Some sp)
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto simp: valid_ready_qs_def in_ready_q_def vs_all_heap_simps)

lemma set_tcb_sched_context_valid_release_q_Some: (* when ref is in release_queue *)
  "\<lbrace>\<lambda>s. valid_release_q s
        \<and> (in_release_q ref s \<longrightarrow> is_active_sc sp s
                                  \<and> sc_ready_times_of s sp = tcb_ready_times_of s ref) \<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref (Some sp)
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (clarsimp simp: valid_release_q_def vs_all_heap_simps in_release_q_def sc_ready_time_eq_iff
                 elim!: sorted_release_qE)
  by (auto simp: tcb_ready_times_defs map_project_simps opt_map_simps map_join_simps)

lemma set_tcb_sched_context_simple_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and simple_sched_action\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp
           simp: weak_valid_sched_action_def simple_sched_action_def vs_all_heap_simps)

lemma set_tcb_obj_ref_sc_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. sc_not_in_release_q scp s \<and> (sc_opt = Some scp \<longrightarrow> not_in_release_q ref s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref sc_opt
   \<lbrace>\<lambda>_ s. sc_not_in_release_q scp s\<rbrace>"
  by(wpsimp wp: valid_sched_wp) (auto simp: vs_all_heap_simps split: if_splits)

lemma set_tcb_sched_context_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref scptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def wp: set_tcb_sched_context_simple_weak_valid_sched_action)

lemma set_tcb_sched_context_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not ref\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp
           simp: weak_valid_sched_action_def scheduler_act_not_def vs_all_heap_simps)

lemma set_tcb_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action
    and (\<lambda>s. scheduler_action s = switch_thread ref
             \<longrightarrow> (\<exists>scp. scp_opt = Some scp \<and> released_sc_at scp s))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref scp_opt
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp
           simp: weak_valid_sched_action_def obj_at_kh_kheap_simps vs_all_heap_simps)

lemma set_tcb_sched_context_valid_sched_action_Some:
  "\<lbrace>\<lambda>s. valid_sched_action s
         \<and> (scheduler_action s = switch_thread ref \<longrightarrow> released_sc_at scp s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref (Some scp)
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def wp: set_tcb_sched_context_weak_valid_sched_action)

lemma set_tcb_sched_context_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and scheduler_act_not ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref scp
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def wp: set_tcb_sched_context_weak_valid_sched_action_act_not)

lemma set_tcb_sched_context_None_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread S)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update thread None
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps)
  by (auto elim!: valid_blockedE' simp: vs_all_heap_simps split: if_splits)

lemma set_tcb_sched_context_None_valid_blocked_except_set_const:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update thread None
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_None_valid_blocked_except_set)

lemma set_tcb_sched_context_valid_blocked_Some':
  "\<lbrace>valid_blocked_except_set (insert t S) and
    (\<lambda>s. pred_map runnable (tcb_sts_of s) t \<and> is_active_sc sp s
         \<longrightarrow> t \<in> S \<or> in_ready_q t s \<or> in_release_q t s
             \<or> t = cur_thread s \<or> scheduler_action s = switch_thread t)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sp)
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps)
  by (auto elim!: valid_blockedE' split: if_splits simp: vs_all_heap_simps in_ready_q_def in_release_q_def)

lemma set_tcb_sched_context_valid_blocked_Some:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. pred_map runnable (tcb_sts_of s) t \<and> is_active_sc sp s
         \<longrightarrow> t \<in> S \<or> in_ready_q t s \<or> in_release_q t s
             \<or> t = cur_thread s \<or> scheduler_action s = switch_thread t)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sp)
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_blocked_Some')

lemma set_tcb_sched_context_valid_blocked:
  "\<lbrace>valid_blocked and
    (\<lambda>s. case sc_opt of Some sp \<Rightarrow>
            not_queued t s \<and> not_in_release_q t s \<longrightarrow> (\<not> st_tcb_at active t s) \<or> \<not> is_sc_active sp s
          | _ \<Rightarrow> True)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc_opt \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  by (auto simp: valid_blocked_defs obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps
                 not_queued_def not_in_release_q_def)

lemma set_tcb_sched_context_Some_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some s)
   \<lbrace>\<lambda>_. valid_blocked_except t\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps)
  by (auto simp: valid_blocked_defs vs_all_heap_simps)

(* FIXME: move *)
lemma bool_to_bool_impE:
  "N P \<Longrightarrow> N (P \<longrightarrow> Q) \<Longrightarrow> N Q"
  by (rule bool_to_bool_cases[of N]; simp)

\<comment> \<open>Neither of the next two lemmas seems to be stronger than the other.\<close>
lemma set_tcb_sc_update_bound_sc_obj_tcb_at_eq':
  "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)
        \<and> (t' = t \<longrightarrow> N (bound_sc_obj_tcb_at (P (cur_time s)) t' s
                          \<longrightarrow> (\<exists>scp. scopt = Some scp
                                     \<and> pred_map (P (cur_time s)) (sc_refill_cfgs_of s) scp)))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t scopt
   \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (rule bool_to_bool_cases[of N]
         ; clarsimp simp: obj_at_kh_kheap_simps pred_map2'_pred_maps vs_all_heap_simps
                    cong: conj_cong)
  by auto

lemma set_tcb_sc_update_bound_sc_obj_tcb_at_eq:
  "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)
        \<and> (t' = t \<longrightarrow> bound_sc_obj_tcb_at (P (cur_time s)) t' s
                       = (\<exists>scp. scopt = Some scp
                                 \<and> pred_map (P (cur_time s)) (sc_refill_cfgs_of s) scp))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t scopt
   \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  by (auto elim!: rsubst[of N]
            simp: pred_map2'_pred_maps obj_at_kh_kheap_simps vs_all_heap_simps
            cong: option.case_cong conj_cong)

lemma set_tcb_pred_tcb_const:
  "\<forall>tcb. p (tcb_to_itcb (f (\<lambda>_. val) tcb)) = p (tcb_to_itcb (tcb)) \<Longrightarrow>
  set_tcb_obj_ref f ref val \<lbrace>(\<lambda>s. Q (pred_tcb_at p P t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma set_tcb_obj_ref_obj_at_const:
  " \<forall>tcb. P (TCB (f (\<lambda>_. val) tcb)) = P (TCB (tcb)) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q (obj_at P t s)\<rbrace> set_tcb_obj_ref f ref val \<lbrace>\<lambda>_. (\<lambda>s. Q (obj_at P t s))::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_obj_ref_wp, clarsimp simp: obj_at_def)

lemma set_sc_obj_ref_obj_at_const:
  "\<forall>sc n. P (SchedContext (f (\<lambda>_. val) sc) n) = P (SchedContext ( sc) n) \<Longrightarrow>
  \<lbrace>\<lambda>s. Q (obj_at P t s)\<rbrace> set_sc_obj_ref f ref val \<lbrace>\<lambda>_. (\<lambda>s. Q (obj_at P t s))::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: update_sched_context_wp, clarsimp simp: obj_at_def)

lemma set_tcb_active_sc_tcb_at_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>_. val) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref val \<lbrace>(\<lambda>s. Q (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def cong: conj_cong)
  by auto

lemma set_sc_active_sc_tcb_at_const:
  "\<forall>sc. sc_refill_max (f (\<lambda>_. val) sc) = sc_refill_max (sc) \<Longrightarrow>
  set_sc_obj_ref f ref val \<lbrace>(\<lambda>s. Q (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def cong: conj_cong)
  by auto

lemma set_tcb_budget_sufficient_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>_. val) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref val \<lbrace>(\<lambda>s. Q (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def  cong: conj_cong)
  by auto

lemma set_sc_budget_sufficient_const:
  "\<forall>sc. sc_refills (f (\<lambda>_. val) sc) = sc_refills (sc) \<Longrightarrow>
  set_sc_obj_ref f ref val \<lbrace>(\<lambda>s. Q (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def  cong: conj_cong)
  by auto

lemma set_tcb_obj_ref_budget_ready_const:
  "\<forall>tcb. tcb_sched_context (f (\<lambda>_. val) tcb) = tcb_sched_context tcb \<Longrightarrow>
  set_tcb_obj_ref f ref val \<lbrace>(\<lambda>s. Q (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def  cong: conj_cong)
  by auto

lemma set_sc_obj_ref_budget_ready_const:
  "\<forall>sc. r_time (refill_hd (f (\<lambda>_. val) sc)) = r_time (refill_hd (sc)) \<Longrightarrow>
  set_sc_obj_ref f ref val \<lbrace>(\<lambda>s. Q (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule back_subst[where P=Q])
  apply (clarsimp simp: vs_all_heap_simps obj_at_def refill_ready_def cong: conj_cong)
  by auto

lemma set_tcb_sc_update_bound_sc_obj_tcb_at:
  "\<lbrace>\<lambda>s. (tptr \<noteq> t \<longrightarrow> bound_sc_obj_tcb_at (P (cur_time s)) t s)
        \<and> (tptr = t \<longrightarrow> pred_map (P (cur_time s)) (sc_refill_cfgs_of s) scp)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
   \<lbrace>\<lambda>rv s. bound_sc_obj_tcb_at (P (cur_time s)) t s\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (case_tac "tptr = t"; clarsimp simp: vs_all_heap_simps obj_at_def)
  by (rule_tac x=ref' in exI, fastforce)

lemmas set_tcb_sc_update_active_sc_tcb_at =
  set_tcb_sc_update_bound_sc_obj_tcb_at[where P="\<lambda>_. active_scrc", folded obj_at_kh_kheap_simps]

lemma set_tcb_sc_update_bound_sc_obj_tcb_at_neq:
  "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s) \<and> t \<noteq> tptr \<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr scopt
   \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s)\<rbrace>"
  by (wpsimp wp: set_tcb_sc_update_bound_sc_obj_tcb_at_eq)

lemma set_tcb_sc_update_active_sc_tcb_at_eq:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and>
   (active_sc_tcb_at t s \<longleftrightarrow> (\<exists>scp. scopt = Some scp \<and> is_sc_active scp s)) \<rbrace>
      set_tcb_obj_ref tcb_sched_context_update t scopt \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp simp: obj_at_kh_kheap_simps wp: set_tcb_sc_update_bound_sc_obj_tcb_at_eq)

\<comment> \<open>update_sched_context, set_refills\<close>

(* FIXME RT: move *)
definition heap_upd :: "('v \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> 'a \<rightharpoonup> 'v" where
  "heap_upd f ref heap \<equiv> \<lambda>x. if x = ref then map_option f (heap ref) else heap x"

(* FIXME RT: move *)
lemma heap_upd_id[simp]:
  "heap_upd id ref = id"
  by (fastforce simp: heap_upd_def map_option.id)

(* FIXME RT: figure out a systematic way to generate rules like these. *)
lemma sc_heap_proj_known_sc:
  assumes "kh scp = Some (SchedContext sc n)"
  shows "P (sc_refill_cfgs_of_kh kh scp) = P (Some (sc_refill_cfg_of sc))"
    and "Q (sc_tcbs_of_kh kh scp) = Q (Some (sc_tcb sc))"
    and "R (sc_replies_of_kh kh scp) = R (Some (sc_replies sc))"
  by (rule arg_cong[where f=P] arg_cong[where f=Q] arg_cong[where f=R], simp add: vs_all_heap_simps assms)+

lemma update_sched_context_sc_heap:
  "\<lbrace>\<lambda>s. \<forall>sc. scs_of s scp = Some sc \<longrightarrow> P (scs_of s(scp \<mapsto> f sc))\<rbrace>
   update_sched_context scp f
   \<lbrace>\<lambda>rv s. P (scs_of s)\<rbrace>"
  by (wpsimp wp: update_sched_context_wp
           simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps sc_heap.all_simps)

lemma update_sched_context_valid_sched_pred':
  assumes "\<And>sc. sc_refill_cfg_of (f sc) = g (sc_refill_cfg_of sc)"
  assumes "\<And>sc. sc_tcb (f sc) = h (sc_tcb sc)"
  assumes "\<And>sc. sc_replies (f sc) = k (sc_replies sc)"
  shows "\<lbrace>\<lambda>s. pred_map \<top> (scs_of s) scp
              \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                    (heap_upd h scp (sc_tcbs_of s))
                    (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                    (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
                    (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                    (heap_upd g scp (sc_refill_cfgs_of s)) (heap_upd k scp (sc_replies_of s))\<rbrace>
         update_sched_context scp f
         \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: update_sched_context_wp
           simp: fun_upd_def heap_upd_def obj_at_kh_kheap_simps vs_all_heap_simps
                 sc_heap_proj_known_sc assms)

lemmas update_sched_context_valid_sched_pred =
  update_sched_context_valid_sched_pred'[THEN hoare_drop_assertion]

lemmas update_sched_context_valid_sched_pred_inv =
  update_sched_context_valid_sched_pred[where g=id and h=id and k=id and f="\<lambda>sc. upd (f sc) sc" for upd f
                                        , simplified]

lemmas update_sched_context_valid_sched_pred_invs[wp] =
  update_sched_context_valid_sched_pred_inv[where upd=sc_consumed_update, simplified]
  update_sched_context_valid_sched_pred_inv[where upd=sc_ntfn_update, simplified]
  update_sched_context_valid_sched_pred_inv[where upd=sc_badge_update, simplified]
  update_sched_context_valid_sched_pred_inv[where upd=sc_yield_from_update, simplified]

lemmas update_sc_refills_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_refills_update f" and g="scrc_refills_update f" and h=id and k=id for f, simplified]

lemmas update_sc_refill_max_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_refill_max_update f" and g="scrc_refill_max_update f" and h=id and k=id for f, simplified]

lemmas update_sc_period_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_period_update f" and g="scrc_period_update f" and h=id and k=id for f, simplified]

lemmas update_sc_budget_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_budget_update f" and g="scrc_budget_update f" and h=id and k=id for f, simplified]

lemmas update_sc_refill_cfg_valid_sched_misc =
  update_sched_context_valid_sched_pred
    [where h=id and k=id
       and P="\<lambda>cons csc ep_send_qs ep_recv_qs sc_tcbs ctime cdom ct it rqs rlq sa lmt etcbs sts scps faults _ repl.
                P cons csc ep_send_qs ep_recv_qs sc_tcbs ctime cdom ct it rqs rlq sa lmt etcbs sts scps faults repl :: bool" for P
     , simplified]

lemmas update_sc_refill_cfg_valid_sched_miscs[wp] =
  update_sc_refill_cfg_valid_sched_misc[where f="sc_refills_update f" and g="scrc_refills_update f" for f, simplified]
  update_sc_refill_cfg_valid_sched_misc[where f="sc_refill_max_update f" and g="scrc_refill_max_update f" for f, simplified]
  update_sc_refill_cfg_valid_sched_misc[where f="sc_period_update f" and g="scrc_period_update f" for f, simplified]
  update_sc_refill_cfg_valid_sched_misc[where f="sc_budget_update f" and g="scrc_budget_update f" for f, simplified]

lemmas update_sc_tcb_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_tcb_update f" and g=id and h=f and k=id for f, simplified]

lemmas update_sc_tcb_valid_sched_misc[wp] =
  update_sc_tcb_valid_sched_pred[where P="\<lambda>cons csc ep_send_qs ep_recv_qs _. P cons csc ep_send_qs ep_recv_qs :: valid_sched_t" for P]

lemmas update_sc_replies_valid_sched_pred[valid_sched_wp] =
  update_sched_context_valid_sched_pred
    [where f="sc_replies_update f" and g=id and h=id and k=f for f, simplified]

lemmas update_sc_replies_valid_sched_misc[wp] =
  update_sc_replies_valid_sched_pred[where P="\<lambda>cons csc ep_send_qs ep_recv_qs sc_tcbs ctime cdom ct it rqs rlq sa lmt etcbs sts scps faults rcs _.
                                             P cons csc ep_send_qs ep_recv_qs sc_tcbs ctime cdom ct it rqs rlq sa lmt etcbs sts scps faults rcs :: bool" for P]

lemma set_refills_valid_sched_pred':
  "\<lbrace>\<lambda>s. pred_map \<top> (scs_of s) scp
        \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
              (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
              (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
              (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
              (heap_upd (scrc_refills_update (\<lambda>_. refills)) scp (sc_refill_cfgs_of s))
              (sc_replies_of s)\<rbrace>
   set_refills scp refills
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_refills_def fun_upd_def heap_upd_def vs_all_heap_simps sc_heap_proj_known_sc
               wp: update_sched_context_valid_sched_pred'
                     [where f="sc_refills_update f" and g="scrc_refills_update f" and h=id and k=id for f, simplified])

lemmas set_refills_valid_sched_pred[valid_sched_wp] =
  set_refills_valid_sched_pred'[THEN hoare_drop_assertion]

lemma update_sched_context_valid_sched_misc[wp]:
  "update_sched_context scp f \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                                     (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                                     (ready_queues s) (release_queue s) (scheduler_action s)
                                     (last_machine_time_of s) (tcbs_of s)\<rbrace>"
  by (wpsimp wp: update_sched_context_wp
           simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps tcb_heap.all_simps)

lemma set_refills_valid_sched_misc[wp]:
  "set_refills scp refills \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                                  (sc_tcbs_of s) (sc_replies_of s) (cur_time s) (cur_domain s)
                                  (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
                                  (scheduler_action s) (last_machine_time_of s) (tcbs_of s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=sc_tcbs_of, rotated], wp valid_sched_wp)
  apply (rule hoare_lift_Pf[where f=sc_replies_of, rotated], wp valid_sched_wp)
  by (wpsimp simp: set_refills_def)

lemma update_sched_context_is_sc_active_indep:
  "\<forall>sc. sc_active (f sc) \<longleftrightarrow> sc_active sc
   \<Longrightarrow> update_sched_context ref f \<lbrace>\<lambda>s. P (is_sc_active scp s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def
                  wp: get_object_wp)
  by (clarsimp simp: is_sc_active_def obj_at_def)

lemma sc_tcb_update_is_sc_active[wp]:
  "update_sched_context ref (sc_tcb_update f) \<lbrace>\<lambda>s. P (is_sc_active scp s)\<rbrace>"
  by (clarsimp simp: update_sched_context_is_sc_active_indep)

lemma sc_replies_update_is_sc_active[wp]:
  "update_sched_context ref (sc_replies_update f) \<lbrace>\<lambda>s. P (is_sc_active t s)\<rbrace>"
  by (clarsimp simp: update_sched_context_is_sc_active_indep)

lemma update_sched_context_is_refill_sufficient_indep:
  "\<forall>sc. sc_refills (f sc) = sc_refills sc
   \<Longrightarrow> update_sched_context ref f \<lbrace>is_refill_sufficient y scp\<rbrace>"
  by (wpsimp wp: update_sched_context_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma update_sched_context_is_refill_ready_indep:
  "\<forall>sc. sc_refills (f sc) = sc_refills sc
   \<Longrightarrow> update_sched_context ref f \<lbrace>is_refill_ready scp\<rbrace>"
  by (wpsimp wp: update_sched_context_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma sc_replies_update_sc_tcb_sc_at[wp]:
  "update_sched_context scp (sc_replies_update f) \<lbrace>\<lambda>s. N (sc_tcb_sc_at P t s)\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (auto simp: sc_tcb_sc_at_def pred_tcb_at_def obj_at_def)

lemma set_refills_valid_ready_qs:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and>
    (\<forall>tcb_ptr. pred_map_eq (Some sc_ptr) (tcb_scps_of s) tcb_ptr \<longrightarrow>
               in_ready_q tcb_ptr s \<longrightarrow>
               refill_sufficient 0 (hd refills) \<and> refill_ready (cur_time s) (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce simp: valid_ready_qs_def vs_all_heap_simps in_ready_q_def heap_upd_def)

lemma active_sc_refills_update_eq[simp]:
  "active_sc_tcb_at_pred tcb_scps (heap_upd (scrc_refills_update f) scp sc_refill_cfgs) t
   \<longleftrightarrow> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t"
  apply (clarsimp simp: active_sc_def heap_upd_def pred_map_simps opt_map_simps map_join_simps split: if_splits)
  apply (rule iffI, fastforce)
  apply (clarsimp, rename_tac sc scp')
  apply (rule_tac x="if scp' = scp then scrc_refills_update f sc else sc" in exI)
  by auto

lemma set_refills_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
        \<and> (\<forall>t. heap_ref_eq sc_ptr t (tcb_scps_of s)
               \<longrightarrow> requires_released_if_bound_sc_tcb_at t s
               \<longrightarrow> refill_sufficient 0 (hd refills) \<and> refill_ready (cur_time s) (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (clarsimp simp: elim!: released_ipc_queuesE)
  by (fastforce simp: vs_all_heap_simps heap_upd_def split: if_splits)

lemma set_refills_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and sc_not_in_ready_q sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp wp: set_refills_valid_ready_qs simp: obj_at_kh_kheap_simps in_queues_2_def)

(* FIXME RT: find a nicer calculus for dealing with sorted_release_q *)
lemma set_refills_valid_release_q:
  "\<lbrace>\<lambda>s. valid_release_q s
        \<and> (\<forall>t. pred_map_eq (Some sc_ptr) (tcb_scps_of s) t
               \<longrightarrow> in_release_q t s
               \<longrightarrow> tcb_ready_times_of s t = Some (r_time (hd refills)))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (clarsimp simp: valid_release_q_def heap_upd_def vs_all_heap_simps in_release_q_def)
  apply (rule conjI, fastforce)
  apply (erule sorted_release_qE)
  apply (rule option_eqI)
   subgoal by (auto simp: tcb_ready_times_defs map_project_simps opt_map_simps map_join_simps vs_all_heap_simps)
  apply (drule (1) bspec)
  apply (clarsimp simp: tcb_ready_times_defs map_project_simps opt_map_simps map_join_simps vs_all_heap_simps)
  by (case_tac "ref' = sc_ptr"; fastforce)

lemma set_refills_sc_tcb_sc_at[wp]:
  "set_refills sc_ptr' refills \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp )
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemmas set_refills_budget_ready = set_refills_bound_sc_obj_tcb_at_refills_cur_time[where P="\<lambda>curtime refills. refill_ready curtime (hd refills)"]
lemmas set_refills_budget_sufficient = set_refills_bound_sc_obj_tcb_at_refills_simple[where P="\<lambda>refills. refill_sufficient 0 (hd refills)"]

lemma set_refills_budget_ready_other:
  "\<lbrace>budget_ready t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x \<noteq> (Some sc_ptr)) t s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  by (wpsimp wp: set_refills_budget_ready simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma set_refills_budget_sufficient_other:
  "\<lbrace>budget_sufficient t and
    (\<lambda>s. bound_sc_tcb_at (\<lambda>x. x \<noteq> (Some sc_ptr)) t s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_sufficient t\<rbrace>"
  by (wpsimp wp: set_refills_budget_sufficient simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemmas update_sc_refills_active_sc_tcb_at[wp]
  = bound_sc_obj_tcb_at_update_sched_context_no_change[where P=active_scrc and f="\<lambda>sc. sc\<lparr>sc_refills := f sc\<rparr>" for f, simplified]

lemmas set_refills_active_sc_tcb_at[wp]
  = bound_sc_obj_tcb_at_set_refills_no_change[where P=active_scrc, simplified]

lemma set_refills_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and
    (\<lambda>s. \<forall>tcb_ptr. pred_map_eq (Some sc_ptr) (tcb_scps_of s) tcb_ptr \<longrightarrow>
                   scheduler_action s = switch_thread tcb_ptr \<longrightarrow>
                   refill_sufficient 0 (hd refills) \<and> refill_ready (cur_time s) (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce simp: heap_upd_def weak_valid_sched_action_def vs_all_heap_simps cong: conj_cong)

lemma set_refills_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: set_refills_weak_valid_sched_action
           simp: scheduler_act_not_def) fastforce

lemma set_refills_valid_sched_action:
  "\<lbrace>valid_sched_action and
    (\<lambda>s. \<forall>tcb_ptr. pred_map_eq (Some sc_ptr) (tcb_scps_of s) tcb_ptr \<longrightarrow>
                   scheduler_action s = switch_thread tcb_ptr \<longrightarrow>
                   refill_sufficient 0 (hd refills) \<and> refill_ready (cur_time s) (hd refills))\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def wp: set_refills_weak_valid_sched_action)

lemma set_refills_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and sc_scheduler_act_not sc_ptr\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: scheduler_act_not_def obj_at_def
               wp: set_refills_valid_sched_action) fastforce

lemma set_refills_valid_blocked_except_set[wp]:
  "set_refills sc_ptr refills \<lbrace>valid_blocked_except_set S\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto elim!: valid_blockedE' simp: heap_upd_def vs_all_heap_simps split: if_splits)

lemma set_refills_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills and
    (\<lambda>s. is_active_sc sc_ptr s \<longrightarrow>
         pred_map (\<lambda>sc. cfg_valid_refills (sc\<lparr>scrc_refills := refills\<rparr>)) (sc_refill_cfgs_of s) sc_ptr
         \<and> pred_map (\<lambda>sc. cfg_bounded_release_time (cur_time s) (sc\<lparr>scrc_refills := refills\<rparr>))
                          (sc_refill_cfgs_of s) sc_ptr)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>rv. active_sc_valid_refills\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (clarsimp simp: active_sc_valid_refills_def vs_all_heap_simps heap_upd_def)

lemma set_refills_active_reply_scs[wp]:
  "set_refills scp refills \<lbrace>active_reply_scs\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto elim!: active_reply_scsE simp: heap_upd_def vs_all_heap_simps)

lemma set_refills_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s
        \<and> (\<forall>t. pred_map_eq (Some scp) (tcb_scps_of s) t
               \<longrightarrow> (scheduler_action s = switch_thread t \<or> in_ready_q t s \<or> requires_released_if_bound_sc_tcb_at t s
                    \<longrightarrow> refill_sufficient 0 (hd refills) \<and> refill_ready (cur_time s) (hd refills))
                   \<and> (in_release_q t s \<longrightarrow> tcb_ready_times_of s t = Some (r_time (hd refills))))
        \<and> (is_active_sc scp s \<longrightarrow>
           pred_map (\<lambda>sc. cfg_valid_refills (sc\<lparr>scrc_refills := refills\<rparr>)) (sc_refill_cfgs_of s) scp \<and>
           pred_map (\<lambda>sc. cfg_bounded_release_time (cur_time s) (sc\<lparr>scrc_refills := refills\<rparr>))
                          (sc_refill_cfgs_of s) scp)\<rbrace>
   set_refills scp refills
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: set_refills_valid_ready_qs set_refills_valid_release_q valid_idle_etcb_lift
                   set_refills_valid_sched_action set_refills_active_sc_valid_refills
                   set_refills_released_ipc_queues)

lemma set_refills_valid_sched_not_in:
  "\<lbrace>valid_sched and sc_not_in_release_q sc_ptr and
     sc_not_in_ready_q sc_ptr and sc_scheduler_act_not sc_ptr and sc_not_in_ep_q sc_ptr
    and (\<lambda>s. is_active_sc sc_ptr s
             \<longrightarrow> pred_map (\<lambda>sc. cfg_valid_refills (sc\<lparr>scrc_refills := refills\<rparr>)) (sc_refill_cfgs_of s) sc_ptr
                 \<and> pred_map (\<lambda>sc. cfg_bounded_release_time (cur_time s) (sc\<lparr>scrc_refills := refills\<rparr>))
                          (sc_refill_cfgs_of s) sc_ptr)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_refills_valid_release_q set_refills_active_sc_valid_refills
                 set_refills_valid_ready_qs_not_queued
                 set_refills_valid_sched_action_act_not
                 set_refills_released_ipc_queues
           simp: pred_map_ipc_queued_thread_state_iff)

\<comment> \<open>sched_context_donate\<close>

crunches sched_context_donate
  for consumed_time[wp]: "\<lambda>s. P (consumed_time s)"
  and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and last_machine_time_of[wp]: "\<lambda>s. P (last_machine_time_of s)"
  and ep_send_qs_of[wp]: "\<lambda>s. P (ep_send_qs_of s)"
  and ep_recv_qs_of[wp]: "\<lambda>s. P (ep_recv_qs_of s)"

lemma sched_context_donate_etcb_heap[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: tcb_release_remove_wp)

lemma sched_context_donate_tcb_st_heap[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (tcb_sts_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: tcb_release_remove_wp)

lemma sched_context_donate_tcb_fault_heap[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (tcb_faults_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: tcb_release_remove_wp)

lemma sched_context_donate_sc_refill_cfg_heap[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: tcb_release_remove_wp)

lemma sched_context_donate_sc_replies_heap[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (sc_replies_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: tcb_release_remove_wp)

lemma sched_context_donate_valid_sched_misc[wp]:
  "sched_context_donate scp t \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                                     (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                                     (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
                                     (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=consumed_time, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=cur_sc, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=ep_send_qs_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=ep_recv_qs_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=cur_time, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=cur_domain, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=cur_thread, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=idle_thread, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=last_machine_time_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=etcbs_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=tcb_sts_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=tcb_faults_of, rotated], wpsimp)
  apply (rule hoare_lift_Pf[where f=sc_refill_cfgs_of, rotated], wpsimp)
  by wpsimp

(* FIXME RT: move to DetSchedInvs_AI *)
definition
  sc_is_round_robin :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_is_round_robin = sc_at_pred (\<lambda>sc. (sc_period sc = sc_budget sc))"

crunches sched_context_donate
  for simple[wp]: simple_sched_action
  (simp: crunch_simps)

(* FIXME RT: this naming is inconsistent *)
abbreviation cur_sc_offset_sufficient :: "time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "cur_sc_offset_sufficient usage s \<equiv>
      is_refill_sufficient usage (cur_sc s) s"

abbreviation cur_sc_budget_sufficient :: "'z::state_ext state \<Rightarrow> bool"
where
  "cur_sc_budget_sufficient s \<equiv>
      is_refill_sufficient 0 (cur_sc s) s"

definition cur_sc_not_blocked where
  "cur_sc_not_blocked s \<equiv>
       \<forall>t. pred_map_eq (Some (cur_sc s)) (tcb_scps_of s) t
          \<longrightarrow> ipc_queued_thread t s
          \<longrightarrow> False"

lemma as_user_tcb_arch_inv:
  assumes "\<And>s tcb upd. \<lbrakk> kheap s t = Some (TCB tcb); P s \<rbrakk>
                        \<Longrightarrow> P (kheap_update (\<lambda>kh. kh(t \<mapsto> TCB (tcb_arch_update upd tcb))) s)"
  shows "as_user t m \<lbrace>P\<rbrace>"
  apply (wpsimp simp: as_user_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_ko_at obj_at_def assms cong: abstract_state.fold_congs)

lemma as_user_sk_obj_at_pred:
  assumes "\<And>tcb obj. TCB tcb \<noteq> C obj"
  shows "as_user t m \<lbrace>\<lambda>s. N (sk_obj_at_pred C proj P p s)\<rbrace>"
  by (clarsimp intro!: as_user_tcb_arch_inv simp: sk_obj_at_pred_def2 assms)

lemmas as_user_sk_obj_at_preds[wp] =
  as_user_sk_obj_at_pred[where C=Endpoint, simplified]
  as_user_sk_obj_at_pred[where C=Notification, simplified]
  as_user_sk_obj_at_pred[where C=Reply, simplified]

lemma as_user_valid_sched_pred[wp]:
  "as_user t m \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: as_user_tcb_arch_inv simp: fun_upd_def vs_all_heap_simps)

\<comment> \<open>complete_yield_to\<close>

lemma set_message_info_valid_sched_pred[wp]:
  "set_message_info t info \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_message_info_def)

lemma sched_context_update_consumed_valid_sched_pred[wp]:
  "sched_context_update_consumed scp \<lbrace>valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def wp: update_sched_context_wp)
  by (clarsimp simp: fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps)

lemma set_consumed_valid_sched_pred[wp]:
  "set_consumed scp args \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma complete_yield_to_valid_sched_pred[wp]:
  "complete_yield_to t \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: complete_yield_to_def wp: hoare_drop_imps)

(* FIXME RT: move to DetSchedInvs_AI *)
\<comment> \<open>This version composes with valid_sched_pred rules\<close>
lemma gts_wp':
  "\<lbrace>\<lambda>s. \<forall>st. pred_map_eq st (tcb_sts_of s) t \<longrightarrow> P st s\<rbrace> get_thread_state t \<lbrace>P\<rbrace>"
  by (wpsimp wp: gts_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma handle_arch_fault_reply_cur'[wp]:
  "handle_arch_fault_reply f t x y \<lbrace>cur_tcb :: 'z::state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cur_tcb_def by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: tcb_at_typ_at')

(* FIXME: Move to DetSchedInvs_AI? *)
abbreviation cur_sc_in_release_q_imp_zero_consumed :: "'z state \<Rightarrow> bool" where
  "cur_sc_in_release_q_imp_zero_consumed \<equiv>
    \<lambda>s. \<forall>t. pred_map_eq (Some (cur_sc s)) (tcb_scps_of s) t
            \<longrightarrow> in_release_q t s \<longrightarrow> consumed_time s = 0"

locale DetSchedSchedule_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes kernel_irq_timer_is_kernel_IRQ[simp]:
    "kernel_irq_timer \<notin> non_kernel_IRQs"
  assumes arch_switch_to_thread_valid_sched_pred[wp]:
    "\<And>t P. arch_switch_to_thread t \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_sched_pred[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_idle[wp]:
    "arch_switch_to_idle_thread \<lbrace>valid_idle::'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_valid_sched_pred[wp]:
    "\<And>cap final P. arch_finalise_cap cap final \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes make_arch_fault_msg_valid_sched_pred[wp]:
    "\<And>flt t P. make_arch_fault_msg flt t \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_valid_sched_pred[wp]:
    "\<And>airq P. arch_invoke_irq_control airq \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_valid_sched_pred[wp]:
    "\<And>c t P. arch_post_modify_registers c t \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_valid_sched_pred[wp]:
    "\<And>f t x y P. handle_arch_fault_reply f t x y \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_activate_idle_thread_valid_sched_pred[wp]:
    "\<And>t P. arch_activate_idle_thread t \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  \<comment> \<open>Due to delete_objects in perform_asid_control_invocation,
      arch_perform_invocation doesn't preserve valid_sched_pred\<close>
  assumes arch_perform_invocation_valid_sched[wp]:
    "\<And>i. \<lbrace>invs and valid_sched and ct_active and valid_arch_inv i and
            (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
          arch_perform_invocation i
          \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_cur_sc_tcb_only_sym_bound[wp]:
    "\<And>i. arch_perform_invocation i \<lbrace>cur_sc_tcb_only_sym_bound :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_cur_sc_chargeableE_E[wp]:
    "\<And>i. \<lbrace>cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace> arch_perform_invocation i -, \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  assumes arch_perform_invocation_ct_not_blockedE_E[wp]:
    "\<And>i. \<lbrace>ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace> arch_perform_invocation i -, \<lbrace>\<lambda>_. ct_not_blocked\<rbrace>"
  assumes arch_perform_invocation_valid_sched_misc[wp]:
    "\<And>i P. arch_perform_invocation i
            \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_time s) (cur_domain s) (cur_thread s)
                                     (cur_sc s) (idle_thread s)
                                     (ready_queues s) (release_queue s) (scheduler_action s)
                                     (last_machine_time_of s)\<rbrace>"
  assumes handle_vm_fault_valid_sched_pred[wp]:
    "\<And>t f P. handle_vm_fault t f \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_valid_sched_pred[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_sched_pred[wp] :
    "\<And>c P. arch_post_cap_deletion c \<lbrace>valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  (* FIXME RT: Reframe sc_is_round_robin using heap projections, then the next 2 assumptions are redundant. *)
  assumes arch_switch_to_idle_thread_sc_is_round_robin[wp]:
    "\<And>P t. arch_switch_to_idle_thread \<lbrace>\<lambda>s::'state_ext state. P (sc_is_round_robin t s)\<rbrace>"
  assumes arch_switch_to_thread_sc_is_round_robin[wp]:
    "\<And>P t' t. arch_switch_to_thread t' \<lbrace>\<lambda>s::'state_ext state. P (sc_is_round_robin t s)\<rbrace>"
  assumes prepare_thread_delete_ct_in_state[wp]:
    "\<And>t P. prepare_thread_delete t \<lbrace>ct_in_state P ::det_state \<Rightarrow> _\<rbrace>"
  assumes update_time_stamp_valid_machine_time[wp]:
    "update_time_stamp \<lbrace>valid_machine_time:: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes dmo_getCurrentTime_vmt_sp:
    "\<lbrace>valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
     do_machine_op getCurrentTime
     \<lbrace>\<lambda>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1)\<rbrace>"

locale DetSchedSchedule_AI_det_ext = DetSchedSchedule_AI "TYPE(det_ext)" +
  assumes arch_activate_idle_thread_valid_list'[wp]:
    "\<And>t P. arch_activate_idle_thread t \<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace>"
  assumes arch_switch_to_thread_valid_list'[wp]:
    "\<And>t P. arch_switch_to_thread t \<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_list'[wp]:
    "\<And>P. arch_switch_to_idle_thread \<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace>"
  assumes arch_switch_to_thread_exst[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (exst s)\<rbrace>"

context DetSchedSchedule_AI begin

sublocale arch_switch_to_thread: valid_sched_pred_locale state_ext_t "arch_switch_to_thread t" by unfold_locales wp
sublocale arch_switch_to_idle_thread: valid_sched_pred_locale state_ext_t arch_switch_to_idle_thread by unfold_locales wp
sublocale arch_finalise_cap: valid_sched_pred_locale state_ext_t "arch_finalise_cap cap final" by unfold_locales wp
sublocale make_arch_fault_msg: valid_sched_pred_locale state_ext_t "make_arch_fault_msg flt t" by unfold_locales wp
sublocale arch_invoke_irq_control: valid_sched_pred_locale state_ext_t "arch_invoke_irq_control airq" by unfold_locales wp
sublocale arch_post_modify_registers: valid_sched_pred_locale state_ext_t "arch_post_modify_registers c t" by unfold_locales wp
sublocale handle_arch_fault_reply: valid_sched_pred_locale state_ext_t "handle_arch_fault_reply f t x y" by unfold_locales wp
sublocale arch_activate_idle_thread: valid_sched_pred_locale state_ext_t "arch_activate_idle_thread t" by unfold_locales wp
sublocale handle_vm_fault: valid_sched_pred_locale state_ext_t "handle_vm_fault t f" by unfold_locales wp
sublocale prepare_thread_delete: valid_sched_pred_locale state_ext_t "prepare_thread_delete t" by unfold_locales wp
sublocale arch_get_sanitise_register_info: valid_sched_pred_locale state_ext_t "arch_get_sanitise_register_info ft" by unfold_locales wp
sublocale arch_post_cap_deletion: valid_sched_pred_locale state_ext_t "arch_post_cap_deletion c" by unfold_locales wp

lemma switch_to_idle_thread_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (idle_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s)
          (last_machine_time_of s) (etcbs_of s)
          (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def)

lemmas switch_to_idle_thread_valid_sched_misc[wp] =
  switch_to_idle_thread_valid_sched_pred[where P="\<lambda>cont csc sc_tcbs sc_replies ctime cdom ct. P cont csc sc_tcbs sc_replies ctime cdom" for P]

lemma switch_to_idle_thread_ct_not_in_q[wp]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (fastforce simp: valid_ready_qs_def ct_not_in_q_def not_queued_def valid_idle_def
                      pred_tcb_at_def obj_at_def vs_all_heap_simps)

lemma switch_to_idle_thread_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (auto simp: valid_sched_action_def valid_idle_def pred_tcb_at_def obj_at_def
                 is_activatable_def vs_all_heap_simps)

lemma switch_to_idle_thread_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto simp: ct_in_cur_domain_def)

lemma switch_to_idle_thread_ct_not_queued[wp]:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>rv s::'state_ext state. not_queued (cur_thread s) s\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (fastforce simp add: valid_ready_qs_def valid_idle_def in_ready_q_def
                          pred_tcb_at_def obj_at_def vs_all_heap_simps)

lemma switch_to_idle_thread_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (auto simp: valid_blocked_defs ct_in_q_def vs_all_heap_simps)

lemma stit_activatable':
  "\<lbrace>valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. ct_in_state activatable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: switch_to_idle_thread_def ct_in_state_def obj_at_kh_kheap_simps)
  by (auto simp: valid_idle_def pred_tcb_at_def obj_at_def vs_all_heap_simps)

lemma activate_thread_valid_sched_pred_misc[wp]:
  "activate_thread
   \<lbrace>\<lambda>s::'state_ext state. P (cur_time s) (cur_domain s) (ep_send_qs_of s) (ep_recv_qs_of s)
                            (sc_tcbs_of s) (sc_replies_of s) (cur_thread s) (idle_thread s)
                            (ready_queues s) (release_queue s) (last_machine_time_of s)
                            (etcbs_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp gts_wp' simp: activate_thread_def)

lemma activate_thread_valid_ready_qs[wp]:
  "activate_thread \<lbrace>valid_ready_qs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')
  by (clarsimp simp: valid_ready_qs_def vs_all_heap_simps)

lemma activate_thread_valid_release_q[wp]:
  "activate_thread \<lbrace>valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')
  by (clarsimp simp: valid_release_q_def vs_all_heap_simps)

lemma activate_thread_ct_not_in_q[wp]:
  "activate_thread \<lbrace>ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')

lemma activate_thread_valid_sched_action[wp]:
  "activate_thread \<lbrace>valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')
  by (auto simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def vs_all_heap_simps)

lemma activate_thread_ct_in_cur_domain[wp]:
  "activate_thread \<lbrace>ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')

lemma activate_thread_valid_blocked[wp]:
  "activate_thread \<lbrace>valid_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')
  by (auto simp: valid_blocked_defs vs_all_heap_simps)

lemma activate_thread_released_ipc_queues[wp]:
  "activate_thread \<lbrace>released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: valid_sched_wp gts_wp')
  by (clarsimp simp: vs_all_heap_simps elim!: released_ipc_queuesE)

lemma activate_thread_valid_sched[wp]:
  "activate_thread \<lbrace>valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def)

\<comment> \<open>We can't write a wp-style rule, because we don't know how some arch functions update arch state.\<close>
lemma switch_to_thread_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>d p. etcb_eq p d t s \<and> t \<notin> set (release_queue s) \<and> budget_ready t s \<and> budget_sufficient t s
               \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
                     (cur_time s) (cur_domain s) t (idle_thread s)
                     (tcb_sched_ready_q_update d p (tcb_sched_dequeue t) (ready_queues s))
                     (release_queue s) (scheduler_action s) (last_machine_time_of s)
                     (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                     (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: switch_to_thread_def
                  wp: get_tcb_obj_ref_wp valid_sched_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps not_in_release_q_def)

lemma guarded_switch_to_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>d p. etcb_eq p d t s \<and> t \<notin> set (release_queue s) \<and> released_sc_tcb_at t s
               \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
                     (cur_time s) (cur_domain s) t (idle_thread s)
                     (tcb_sched_ready_q_update d p (tcb_sched_dequeue t) (ready_queues s))
                     (release_queue s) (scheduler_action s) (last_machine_time_of s)
                     (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                     (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   guarded_switch_to t
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def released_sc_tcb_at_def
               wp: valid_sched_wp thread_get_wp' is_schedulable_wp')

lemma switch_to_thread_valid_sched_misc[wp]:
  "switch_to_thread t
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                            (sc_tcbs_of s) (sc_replies_of s) (cur_time s) (cur_domain s)
                            (idle_thread s) (release_queue s) (scheduler_action s)
                            (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
                            (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma guarded_switch_to_valid_sched_misc[wp]:
  "guarded_switch_to t
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (ep_send_qs_of s ) (ep_recv_qs_of s)
                            (sc_tcbs_of s) (sc_replies_of s) (cur_time s) (cur_domain s)
                            (idle_thread s) (release_queue s) (scheduler_action s)
                            (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s)
                            (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

crunches switch_to_thread
  for valid_ready_qs[wp]: "valid_ready_qs::'state_ext state \<Rightarrow> _"
  (ignore: tcb_sched_action wp: hoare_drop_imp tcb_sched_dequeue_valid_ready_qs)

end

lemma tcb_sched_dequeue_ct_not_in_q_2_ct_upd:
  "\<lbrace>valid_ready_qs\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) thread\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce simp: valid_ready_qs_def ct_not_in_q_def in_queues_2_def tcb_sched_dequeue_def
                      etcbs.all_simps)

lemma tcb_sched_dequeue_valid_sched_action_2_ct_upd:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> is_activatable_2 thread (scheduler_action s) (tcb_sts_of s)\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. valid_sched_action_2 True {} (cur_time s) (scheduler_action s) thread (cur_domain s)
                               (release_queue s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s)
                               (sc_refill_cfgs_of s)\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def valid_sched_action_def split: option.split)
  done

lemma tcb_dequeue_not_queued:
  "\<lbrace>valid_ready_qs\<rbrace> tcb_sched_action tcb_sched_dequeue tptr \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
     (fastforce simp: valid_ready_qs_def vs_all_heap_simps valid_sched_wpsimps)

lemma tcb_release_remove_not_in_release_q[wp]:
  "tcb_release_remove tptr \<lbrace>not_in_release_q t\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def not_in_release_q_def tcb_sched_dequeue_def)

lemma tcb_release_remove_not_in_release_q'[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_release_remove tptr \<lbrace>\<lambda>_. not_in_release_q tptr\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma tcb_dequeue_not_queued_gen:
  "tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>not_queued tptr\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps not_queued_def)

context DetSchedSchedule_AI begin

lemma switch_to_thread_ct_not_queued[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv. ct_not_queued::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce simp: valid_ready_qs_def vs_all_heap_simps valid_sched_wpsimps)

lemma switch_to_thread_ct_not_in_q[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q::'state_ext state \<Rightarrow> _\<rbrace>"
  by (simp add: hoare_post_imp[OF _ switch_to_thread_ct_not_queued])

lemma switch_to_thread_ct_not_in_release_q[wp]:
  "\<lbrace>\<top>\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::'state_ext state. ct_not_in_release_q s\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: in_release_q_def)

end

lemma tcb_sched_action_dequeue_ct_in_cur_domain':
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_ s. ct_in_cur_domain (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  by (wpsimp wp: tcb_sched_action_wp)

context DetSchedSchedule_AI begin

lemma switch_to_thread_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and is_activatable t\<rbrace>
     switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched_action::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: tcb_sched_dequeue_valid_sched_action_2_ct_upd hoare_drop_imp
          simp: switch_to_thread_def)

lemma switch_to_thread_ct_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
  switch_to_thread thread \<lbrace>\<lambda>_. ct_in_cur_domain::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma switch_to_thread_valid_blocked[wp]:
  "\<lbrace>valid_blocked
    and (\<lambda>s. active_sc_tcb_at (cur_thread s) s \<and> ct_not_in_release_q s
             \<longrightarrow> ct_in_q s)\<rbrace>
   switch_to_thread thread
   \<lbrace>\<lambda>_. valid_blocked::'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce simp: valid_sched_wpsimps in_ready_q_def ct_in_q_def runnable_eq_active
               elim!: valid_blockedE')

lemma switch_to_thread_ready_or_release[wp]:
  "switch_to_thread t \<lbrace>ready_or_release :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding switch_to_thread_def
  apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp)
  by (clarsimp simp: is_tcb dest!: get_tcb_SomeD)

lemma switch_to_thread_valid_sched:
  "\<lbrace>is_activatable t and in_cur_domain t and valid_sched_action and valid_ready_qs
    and valid_release_q and ready_or_release and valid_blocked and valid_idle_etcb
    and released_ipc_queues and valid_machine_time and active_reply_scs and active_sc_valid_refills
    and (\<lambda>s. (active_sc_tcb_at (cur_thread s) s \<and> ct_not_in_release_q s)
             \<longrightarrow> ct_in_q s)\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def, simp add: ct_in_cur_domain_def)

crunch valid_idle[wp]: switch_to_idle_thread "valid_idle :: 'state_ext state \<Rightarrow> _"

end

lemma guarded_switch_to_lift:
  assumes "\<lbrace>P\<rbrace> switch_to_thread thread \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> guarded_switch_to thread \<lbrace>Q\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def wp: assms thread_get_wp' is_schedulable_wp')

lemma next_domain_valid_idle[wp]:
  "\<lbrace> valid_idle \<rbrace> next_domain \<lbrace> \<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: next_domain_def wp: dxo_wp_weak)
  by (clarsimp simp: valid_idle_def Let_def)

lemma enqueue_thread_queued:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_ s. \<exists>d prio. thread \<in> set (ready_queues s d prio)\<rbrace>"
  by (wpsimp wp: tcb_sched_action_wp simp: tcb_sched_enqueue_def etcbs.all_simps) auto

(* FIXME move *)
lemma in_release_q_valid_blocked_ct_upd:
  "\<lbrakk>in_release_q (cur_thread s) s; valid_blocked s\<rbrakk> \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  by (clarsimp elim!: valid_blockedE')

context DetSchedSchedule_AI begin

lemma switch_to_idle_thread_valid_sched:
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q
      and valid_blocked and ct_in_q and valid_idle_etcb and released_ipc_queues and ready_or_release
      and active_reply_scs and valid_machine_time and active_sc_valid_refills\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def)

crunch etcb_at[wp]: choose_thread "etcb_at P t :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

lemma choose_thread_valid_sched[wp]:
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q and ready_or_release
    and valid_blocked and ct_in_q and valid_idle_etcb and released_ipc_queues and active_reply_scs
    and valid_machine_time
    and active_sc_valid_refills\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: choose_thread_def
                  wp: switch_to_idle_thread_valid_sched guarded_switch_to_lift
                      switch_to_thread_valid_sched)
  apply (clarsimp simp: valid_ready_qs_def next_thread_def is_activatable_2_def
                 dest!: next_thread_queued)
  by (fastforce simp: tcb_sts.pred_map_simps in_cur_domain_def etcb_at_def etcbs.pred_map_simps)

end

lemma do_extended_op_valid_sched_pred[wp]:
  "do_extended_op eop \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: do_extended_op_def)

\<comment> \<open>We leave the resulting cur_domain unspecified, since we can't specify it in terms of state
    projections that are part of valid_sched_pred\<close>
lemma next_domain_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>cdom'. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
                  (cur_time s) cdom' (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
                  (scheduler_action s) (last_machine_time_of s)
                  (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                  (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   next_domain
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: next_domain_def Let_def)

crunches next_domain
  for valid_sched_misc[wp]: "\<lambda>s. P (consumed_time s) (cur_sc s)
                                   (sc_tcbs_of s) (sc_replies_of s) (cur_time s) (cur_thread s)
                                   (idle_thread s) (ready_queues s) (release_queue s)
                                   (scheduler_action s) (last_machine_time_of s) (kheap s)"
  (simp: Let_def wp: dxo_wp_weak)

lemma next_domain_valid_sched_action:
  "\<lbrace>\<lambda>s. scheduler_action s = choose_new_thread\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

context DetSchedSchedule_AI begin
lemma switch_to_thread_cur_in_cur_domain[wp]:
  "\<lbrace>in_cur_domain t\<rbrace> switch_to_thread t \<lbrace>\<lambda>_ s::'state_ext state. in_cur_domain (cur_thread s) s\<rbrace>"
  by (wpsimp wp: valid_sched_wp)
end

lemma tcb_sched_enqueue_cur_ct_in_q:
  "\<lbrace>\<lambda>s. cur = cur_thread s\<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps in_queues_2_def ct_in_q_def)

lemma tcb_sched_enqueue_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: ct_in_q_def valid_sched_wpsimps)

lemma tcb_sched_append_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_append cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: ct_in_q_def valid_sched_wpsimps)

context DetSchedSchedule_AI begin

lemma switch_to_idle_thread_ct_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. valid_release_q s \<and> valid_idle s\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>rv. ct_not_in_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_idle_def valid_release_q_def pred_tcb_at_def obj_at_def in_release_q_def
                 vs_all_heap_simps)

lemma switch_to_thread_sched_act_is_cur:
  "\<lbrace>\<lambda>s::'state_ext state. scheduler_action s = switch_thread word\<rbrace>
   switch_to_thread word
   \<lbrace>\<lambda>rv s. scheduler_action s = switch_thread (cur_thread s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

end

lemma set_scheduler_action_switch_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action (switch_thread t) \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: ct_not_in_q_def)
  done

lemma possible_switch_to_valid_sched_misc[wp]:
  "possible_switch_to t \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                               (idle_thread s) (release_queue s) (last_machine_time_of s) (kheap s)\<rbrace>"
  by (wpsimp simp: possible_switch_to_def wp: valid_sched_wp get_tcb_obj_ref_wp thread_get_wp')

abbreviation (input) possible_switch_to_wp where
  "possible_switch_to_wp t P s \<equiv>
    \<forall>d p. etcb_eq p d t s
          \<longrightarrow> (if pred_map_eq None (tcb_scps_of s) t \<or> t \<in> set (release_queue s)
               then P s
               else let enq_t = ready_queues_update (tcb_sched_ready_q_update d p (tcb_sched_enqueue t)) in
                    if d \<noteq> cur_domain s
                    then P (enq_t s)
                    else if scheduler_action s = resume_cur_thread
                         then P (s\<lparr>scheduler_action := switch_thread t\<rparr>)
                         else reschedule_required_wp (\<lambda>s. P (enq_t s)) s)"

lemma possible_switch_to_wp:
  "\<lbrace>possible_switch_to_wp t P\<rbrace> possible_switch_to t \<lbrace>\<lambda>rv. P\<rbrace>"
  supply if_split[split del] if_cong[cong del]
  apply (wpsimp simp: possible_switch_to_def wp: valid_sched_wp get_tcb_obj_ref_wp thread_get_wp')
  apply (simp add: obj_at_def etcbs.pred_map_simps Let_def if_distribR)
  apply (simp add: tcb_scps.pred_map_simps in_queue_2_def)
  by (case_tac "tcb_sched_context tcb = None \<or> t \<in> set (release_queue s)", fastforce, clarsimp)

lemma possible_switch_to_ct_not_in_q:
  "\<lbrace>ct_not_in_q and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace> possible_switch_to t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: possible_switch_to_wp simp: ct_not_in_q_def not_queued_def tcb_sched_enqueue_def)

lemma possible_switch_to_not_it_ct_not_in_q:
  "\<lbrace>\<lambda>s. ct_not_in_q s \<and> ct_in_cur_domain s \<and> t \<noteq> idle_thread s\<rbrace>
   possible_switch_to t
   \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: possible_switch_to_wp
           simp: ct_not_in_q_def in_queues_2_def tcb_sched_enqueue_def ct_in_cur_domain_def
                 vs_all_heap_simps in_cur_domain_def etcb_at_def)

crunch ct_not_in_q[wp]: test_reschedule ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_vcg_if_lift2)

lemma sched_context_donate_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: get_sc_obj_ref_wp)

lemma sched_context_unbind_tcb_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> sched_context_unbind_tcb scp \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp wp: get_sched_context_wp valid_sched_wp
           simp: sched_context_unbind_tcb_def valid_sched_wpsimps in_queues_2_def)

crunch ct_not_in_q[wp]: reply_unlink_sc ct_not_in_q
  (wp: crunch_wps hoare_drop_imps)

crunch ct_not_in_q[wp]: reply_unlink_tcb ct_not_in_q
  (wp: crunch_wps hoare_drop_imps)

lemma reply_remove_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> reply_remove t r \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)
  done

definition choose_thread_spec_2 where
  "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_rcs ct' qs' \<equiv>
    if \<forall>prio. qs cdom prio = []
    then ct' = it \<and> qs' = qs
    else let t = hd (max_non_empty_queue (qs cdom)) in
         \<exists>d' p'. etcb_eq' p' d' etcbs t
                 \<and> ct' = t
                 \<and> qs' = tcb_sched_ready_q_update d' p' (tcb_sched_dequeue t) qs
                 \<and> t \<notin> set rlq
                 \<and> released_sc_tcb_at_pred ctime tcb_scps sc_rcs t"

lemma set_refills_budget_ready_wp:
  "\<lbrace>(\<lambda>s. if bound_sc_tcb_at ((=) (Some sc_ptr)) t s
         then refill_ready (cur_time s) (hd refills)
         else budget_ready t s)\<rbrace>
   set_refills sc_ptr refills
   \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps
                 split: if_splits
                  cong: conj_cong)
  by fastforce


abbreviation choose_thread_spec where
  "choose_thread_spec s \<equiv> choose_thread_spec_2 (cur_domain s) (cur_time s) (idle_thread s)
                                               (ready_queues s) (release_queue s)
                                               (etcbs_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

lemmas choose_thread_spec_def = choose_thread_spec_2_def

context DetSchedSchedule_AI begin

lemma choose_thread_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>ct' qs'. choose_thread_spec s ct' qs'
                  \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                        (sc_tcbs_of s) (cur_time s) (cur_domain s) ct' (idle_thread s) qs'
                        (release_queue s) (scheduler_action s) (last_machine_time_of s)
                        (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                        (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   choose_thread
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: choose_thread_def wp: valid_sched_wp)
  by (auto simp: choose_thread_spec_def Let_def
          split: option.splits list.splits if_splits)

lemma choose_thread_valid_sched_misc[wp]:
  "choose_thread
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                            (sc_tcbs_of s) (sc_replies_of s) (cur_time s) (cur_domain s)
                            (idle_thread s) (release_queue s) (scheduler_action s)
                            (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s)
                            (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma choose_thread_ct_not_queued:
  "\<lbrace> valid_ready_qs and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_ct_not_in_release_q:
  "\<lbrace> valid_release_q and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: switch_to_thread_ct_not_in_release_q guarded_switch_to_lift)

lemma choose_thread_spec_idle_or_was_queued_in_cur_domain:
  "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_rcs ct' qs'
   \<Longrightarrow> ct' = it \<or> (\<exists>p. ct' \<in> set (qs cdom p))"
  by (auto simp: choose_thread_spec_2_def Let_def next_thread_def
          split: if_splits
          dest!: next_thread_queued)

lemma choose_thread_cur_dom_or_idle:
  "\<lbrace> valid_ready_qs \<rbrace>
   choose_thread
   \<lbrace>\<lambda>_ s::'state_ext state. (in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s) \<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce dest!: choose_thread_spec_idle_or_was_queued_in_cur_domain
                 simp: in_cur_domain_def etcb_at_def vs_all_heap_simps valid_ready_qs_def)

lemma choose_thread_ct_activatable:
  "\<lbrace> valid_ready_qs and valid_idle \<rbrace>
   choose_thread
   \<lbrace>\<lambda>_ s::'state_ext state. pred_map activatable (tcb_sts_of s) (cur_thread s)\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (fastforce dest!: choose_thread_spec_idle_or_was_queued_in_cur_domain
                 simp: valid_idle_def pred_tcb_at_def obj_at_def valid_ready_qs_def vs_all_heap_simps)

lemmas choose_thread_ct_activatable' =
  choose_thread_ct_activatable[folded obj_at_kh_kheap_simps]

lemma schedule_choose_new_thread_valid_sched_misc[wp]:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (idle_thread s) (release_queue s) resume_cur_thread (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)
          (sc_replies_of s)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s::'state_ext state. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                              (sc_tcbs_of s) (cur_time s) (idle_thread s) (release_queue s)
                              (scheduler_action s) (last_machine_time_of s) (etcbs_of s)
                              (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)
                              (sc_replies_of s)\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by (wpsimp wp: set_scheduler_action_wp)

end

lemma valid_sched_action_from_choose_thread:
  "scheduler_action s = choose_new_thread \<Longrightarrow> valid_sched_action s"
  unfolding valid_sched_action_def by simp

lemma set_scheduler_action_cnt_simple[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. simple_sched_action \<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_obvious[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action a \<lbrace>\<lambda>_ s. scheduler_action s = a\<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_cnt_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> (\<forall>t. scheduler_action s = switch_thread t \<longrightarrow> in_ready_q t s)\<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: set_scheduler_action_cnt_ct_not_in_q
                   set_scheduler_action_cnt_valid_sched_action
                   set_scheduler_action_cnt_ct_in_cur_domain
                   set_scheduler_action_valid_blocked_const)

lemma append_thread_queued[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_ s. thread \<in> ready_queued_threads s\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (fastforce simp: tcb_sched_append_def vs_all_heap_simps)

(* having is_highest_prio match gets_wp makes it very hard to stop and drop imps etc. *)
definition
  "wrap_is_highest_prio cur_dom target_prio \<equiv> gets (is_highest_prio cur_dom target_prio)"

\<comment> \<open>As for next_domain, we leave the resulting cur_domain unspecified\<close>
abbreviation schedule_choose_new_thread_spec where
  "schedule_choose_new_thread_spec s cdom' \<equiv>
    choose_thread_spec_2 cdom' (cur_time s) (idle_thread s) (ready_queues s) (release_queue s)
                               (etcbs_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

lemmas schedule_choose_new_thread_spec_def = choose_thread_spec_2_def

(* FIXME: move up *)
lemma choose_thread_spec_valid_ready_qs[valid_sched_wpsimps]:
  assumes "valid_ready_qs_2 qs ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  assumes "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_refill_cfgs ct' qs'"
  shows "valid_ready_qs_2 qs' ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  using assms by (auto simp: valid_ready_qs_def choose_thread_spec_def Let_def tcb_sched_dequeue_def
                      split: if_splits)

lemma choose_thread_spec_ct_not_queued[valid_sched_wpsimps]:
  assumes "valid_ready_qs_2 qs ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  assumes "pred_map idle tcb_sts it"
  assumes "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_refill_cfgs ct' qs'"
  shows "not_queued_2 qs' ct'"
  using assms
  by (fastforce simp: valid_ready_qs_def in_queues_2_def choose_thread_spec_def Let_def
                      pred_map_simps runnable_eq tcb_sched_dequeue_def
               split: if_splits)

lemma valid_idle_idle_thread:
  "valid_idle s \<Longrightarrow> pred_map idle (tcb_sts_of s) (idle_thread s)"
  by (auto simp: valid_idle_def pred_tcb_at_def obj_at_def vs_all_heap_simps)

lemmas choose_thread_spec_ct_not_queued'[valid_sched_wpsimps] =
  choose_thread_spec_ct_not_queued[OF _ valid_idle_idle_thread]

lemma choose_thread_spec_ct_activatable[valid_sched_wpsimps]:
  assumes "valid_ready_qs_2 qs ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  assumes "pred_map idle tcb_sts it"
  assumes "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_refill_cfgs ct' qs'"
  shows "pred_map activatable tcb_sts ct'"
  using assms
  by (fastforce simp: valid_ready_qs_def choose_thread_spec_def Let_def pred_map_simps
                      next_thread_def runnable_eq
               dest!: next_thread_queued
               split: if_splits)

lemmas choose_thread_spec_ct_activatable'[valid_sched_wpsimps] =
  choose_thread_spec_ct_activatable[OF _ valid_idle_idle_thread]

lemma choose_thread_spec_ct_in_cur_domain[valid_sched_wpsimps]:
  assumes "valid_ready_qs_2 qs ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"
  assumes "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_refill_cfgs ct' qs'"
  shows "ct' = it \<or> in_cur_domain_2 ct' cdom etcbs"
  using assms
  by (fastforce simp: valid_ready_qs_def choose_thread_spec_def ct_in_cur_domain_def
                      in_cur_domain_def Let_def etcb_at'_def pred_map_simps
                      next_thread_def runnable_eq
               dest!: next_thread_queued
               split: if_splits)

lemma not_queued_dequeue_but_was_queued_eq:
  assumes "not_queued_2 (tcb_sched_ready_q_update d' p' (tcb_sched_dequeue t') qs) t"
  assumes "in_queues_2 qs t"
  shows "t = t'"
  using assms by (auto simp: in_queues_2_def tcb_sched_dequeue_def split: if_splits)

lemma choose_thread_spec_valid_blocked[valid_sched_wpsimps]:
  assumes "valid_blocked_2 qs rlq choose_new_thread ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes "choose_thread_spec_2 cdom ctime it qs rlq etcbs tcb_scps sc_refill_cfgs ct' qs'"
  assumes "active_sc_tcb_at_pred tcb_scps sc_refill_cfgs ct \<and> not_in_release_q_2 rlq ct
           \<Longrightarrow> ct_in_q_2 ct qs tcb_sts"
  shows "valid_blocked_2 qs' rlq resume_cur_thread ct' tcb_sts tcb_scps sc_refill_cfgs"
  using assms
  by (fastforce simp: choose_thread_spec_def Let_def not_queued_dequeue_but_was_queued_eq
                      ct_in_q_def next_thread_def runnable_eq_active
               dest!: next_thread_queued elim!: valid_blockedE'
               split: if_splits)

lemma set_irq_state_valid_sched_pred[wp]:
  "set_irq_state irq_st irq \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_irq_state_def)

lemma deleted_irq_handler_valid_sched_pred[wp]:
  "deleted_irq_handler irq \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: deleted_irq_handler_def)

lemma cap_swap_valid_sched_pred[wp]:
  "cap_swap cap1 slot1 cap2 slot2 \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: cap_swap_def)

lemma cap_swap_for_delete_valid_sched_pred[wp]:
  "cap_swap_for_delete slot1 slot2 \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: cap_swap_for_delete_def)

crunches commit_domain_time for valid_sched_pred[wp]: "valid_sched_pred_strong P"

context DetSchedSchedule_AI begin

lemma schedule_choose_new_thread_valid_sched_except_domain[valid_sched_wp]:
  "\<lbrace>\<lambda>s. \<forall>cdom' ct' qs'. schedule_choose_new_thread_spec s cdom' ct' qs'
                        \<longrightarrow> P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s)
                              (sc_tcbs_of s) (cur_time s) cdom' ct' (idle_thread s) qs'
                              (release_queue s) resume_cur_thread (last_machine_time_of s)
                              (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
                              (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def wp: valid_sched_wp)

lemma schedule_choose_new_thread_valid_ready_qs[wp]:
  "schedule_choose_new_thread \<lbrace>valid_ready_qs::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

crunches schedule_choose_new_thread
  for ready_or_release[wp]: "ready_or_release :: 'state_ext state \<Rightarrow> _"
  (wp: hoare_drop_imps)

lemma schedule_choose_new_thread_valid_sched:
  "\<lbrace> valid_idle and valid_idle_etcb and valid_ready_qs and valid_release_q
     and ready_or_release and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)
     and (\<lambda>s. active_sc_tcb_at (cur_thread s) s \<and> ct_not_in_release_q s \<longrightarrow> ct_in_q s)
     and released_ipc_queues and active_reply_scs
     and valid_machine_time
     and active_sc_valid_refills\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_sched_wpsimps wp: valid_sched_wp)
  apply (clarsimp simp: ready_or_release_2_def schedule_choose_new_thread_spec_def Let_def
                        in_queues_2_def in_release_q_def
                 split: if_splits
         ; blast?)
  apply (prop_tac "t \<noteq> hd (max_non_empty_queue (ready_queues s cdom'))", fastforce)
  apply (prop_tac "t \<in> set (ready_queues s d' p')")
   using tcb_sched_act_set_simps(3) apply blast
  by blast

lemma schedule_choose_new_thread_ct_not_queued:
  "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def wp: choose_thread_ct_not_queued)

lemma schedule_choose_new_thread_ct_not_in_release_q:
  "\<lbrace>valid_release_q and valid_idle\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def wp: choose_thread_ct_not_in_release_q)

end

(* FIXME: Should tcb_release_enqueue be defined using takeWhile/dropWhile?
          As shown here, they're equivalent for sorted lists, so perhaps it doesn't matter. *)
definition insort_filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort_filter P x xs \<equiv> filter P xs @ x # filter (\<lambda>x. \<not> P x) xs"

definition insort_partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insort_partition P x xs \<equiv> takeWhile P xs @ x # dropWhile P xs"

lemma sorted_filter_takeWhile:
  assumes tr: "transp cmp"
  shows "sorted_wrt cmp xs \<Longrightarrow> filter (\<lambda>x. cmp x y) xs = takeWhile (\<lambda>x. cmp x y) xs"
proof (induct xs)
  case (Cons x xs)
  have xs: "sorted_wrt cmp xs" and x: "\<forall>z\<in>set xs. cmp x z" using Cons.prems by auto
  note eq = Cons.hyps[OF xs, symmetric]
  show ?case
    apply (clarsimp simp: eq filter_empty_conv dest!: bspec[OF x])
    by (drule (1) transpD[OF tr], simp)
qed auto

lemma sorted_not_filter_dropWhile:
  assumes tr: "transp cmp"
  shows "sorted_wrt cmp xs \<Longrightarrow> filter (\<lambda>x. \<not> cmp x y) xs = dropWhile (\<lambda>x. cmp x y) xs"
proof (induct xs)
  case (Cons x xs)
  have xs: "sorted_wrt cmp xs" and x: "\<forall>z\<in>set xs. cmp x z" using Cons.prems by auto
  note eq = Cons.hyps[OF xs, symmetric]
  show ?case
    apply (clarsimp simp: eq filter_id_conv dest!: bspec[OF x])
    by (drule (1) transpD[OF tr], simp)
qed auto

lemma sorted_insort_filter_eq_insort_partition:
  assumes "transp cmp"
  assumes "sorted_wrt cmp xs"
  shows "insort_filter (\<lambda>x. cmp x y) x xs = insort_partition (\<lambda>x. cmp x y) x xs"
  by (auto simp: insort_filter_def insort_partition_def
                 sorted_filter_takeWhile[OF assms] sorted_not_filter_dropWhile[OF assms])

lemma total_reflD:
  "total {(x,y). cmp x y} \<Longrightarrow> reflp cmp \<Longrightarrow> \<not> cmp a b \<Longrightarrow> cmp b a"
  apply (case_tac "a=b")
   apply (fastforce dest: reflpD)
  by (fastforce simp: total_on_def)

lemma sorted_insort_partition:
  assumes tot: "total {(x,y). cmp x y}"
  assumes tr: "transp cmp"
  assumes re: "reflp cmp"
  assumes sorted: "sorted_wrt cmp xs"
  shows "sorted_wrt cmp (insort_partition (\<lambda>x. cmp x z) z xs)"
  unfolding insort_partition_def
  apply (clarsimp simp: sorted_wrt_append, intro conjI)
     apply (subst sorted_filter_takeWhile[symmetric, OF tr sorted])
     apply (rule sorted_wrt_filter, rule sorted)
    apply (clarsimp simp: sorted_not_filter_dropWhile[symmetric, OF tr sorted])
    apply (fastforce dest: total_reflD[OF tot re])
   apply (subst sorted_not_filter_dropWhile[symmetric, OF tr sorted])
   apply (rule sorted_wrt_filter, rule sorted)
  apply (clarsimp, intro conjI)
   apply (erule takeWhile_taken_P)
  apply (clarsimp simp: sorted_not_filter_dropWhile[symmetric, OF tr sorted])
  apply (drule takeWhile_taken_P)
  apply (rule transpD[OF tr], assumption)
  apply (fastforce dest: total_reflD[OF tot re])
  done

lemma sorted_insort_filter:
  assumes tot: "total {(x,y). cmp x y}"
  assumes tr: "transp cmp"
  assumes re: "reflp cmp"
  assumes sorted: "sorted_wrt cmp xs"
  shows "sorted_wrt cmp (insort_filter (\<lambda>x. cmp x z) z xs)"
  apply (subst sorted_insort_filter_eq_insort_partition[OF tr sorted])
  by (rule sorted_insort_partition[OF tot tr re sorted])

definition tcb_release_enqueue_upd :: "(obj_ref \<rightharpoonup> time) \<Rightarrow> obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_release_enqueue_upd tcb_ready_times t \<equiv> insort_filter (\<lambda>t'. img_ord (the \<circ> tcb_ready_times) (\<le>) t' t) t"

lemma map_fst_filter_zip_map_reduce:
  "map fst (filter P (zip xs (map f xs))) = filter (\<lambda>x. P (x, f x)) xs"
  by (induct xs) auto

lemma tcb_release_enqueue_wp':
  "\<lbrace>\<lambda>s. tcb_sc_refill_cfgs_of s t \<noteq> None
         \<longrightarrow> P (release_queue_update (tcb_release_enqueue_upd (tcb_ready_times_of s) t) s)\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: tcb_release_enqueue_def wp: mapM_get_sc_time_wp get_sc_time_wp)
  apply (drule mp, fastforce simp: sc_ready_times_2_def map_project_simps)
  by (auto simp: tcb_release_enqueue_upd_def insort_filter_def map_fst_filter_zip_map_reduce img_ord_def
          elim!: rsubst[of P]
          dest!: map_Some_implies_map_the)

lemmas tcb_release_enqueue_wp[valid_sched_wp] = tcb_release_enqueue_wp'[THEN hoare_drop_assertion]

lemma tcb_release_enqueue_valid_sched_misc[wp]:
  "tcb_release_enqueue t \<lbrace>\<lambda>s. P (consumed_time s) (cur_time s) (cur_domain s) (cur_thread s) (cur_sc s)
                                (idle_thread s) (ready_queues s) (scheduler_action s) (last_machine_time_of s)
                                (kheap s)\<rbrace>"
  by (wpsimp wp: tcb_release_enqueue_wp)

lemma tcb_dequeue_sc_not_in_ready_q[wp]:
  "tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>sc_not_in_ready_q scp\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps vs_all_heap_simps in_queues_2_def)

lemma tcb_dequeue_sc_not_in_ready_q_cur[wp]:
  "tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>\<lambda>s. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wp)

context DetSchedSchedule_AI begin

lemma switch_to_thread_sc_not_in_ready_q[wp]:
  "switch_to_thread t \<lbrace>\<lambda>s::'state_ext state. sc_not_in_ready_q scp s\<rbrace>"
  by (wpsimp simp: switch_to_thread_def get_tcb_obj_ref_def thread_get_def)

lemma switch_to_thread_sc_not_in_ready_q_cur[wp]:
  "switch_to_thread t \<lbrace>\<lambda>s::'state_ext state. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wp)

lemma choose_thread_sc_not_in_ready_q[wp]:
  "choose_thread \<lbrace>sc_not_in_ready_q scp :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_sc_not_in_ready_q_cur[wp]:
  "choose_thread \<lbrace>\<lambda>s::'state_ext state. sc_not_in_ready_q (cur_sc s) s\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: choose_thread_sc_not_in_ready_q guarded_switch_to_lift)

crunch valid_sched[wp]: empty_slot "valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _"
  (simp: unless_def wp: maybeM_inv ignore: set_object)

end

(* valid_sched for refill_budget_check *)
lemma hd_last_length_2: "length ls = 2 \<Longrightarrow> [hd ls, last ls] = ls"
  apply (cases ls; clarsimp)
  by (case_tac list; clarsimp)

(* FIXME: move *)
lemma pred_map_heap_upd_no_change[simp]:
  assumes "\<And>v. P (f v) \<longleftrightarrow> P v"
  shows "pred_map P (heap_upd f ref heap) = pred_map P heap"
  by (rule ext, auto simp: pred_map_simps heap_upd_def assms)

(* FIXME: move *)
crunches refill_budget_check
for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: crunch_wps)

lemma pred_map2_heap_upd_no_change[simp]:
  assumes "\<And>v. P (f v) \<longleftrightarrow> P v"
  shows "pred_map2 P heap' (heap_upd f ref heap) = pred_map2 P heap' heap"
  by (simp add: pred_map2_pred_maps pred_map_heap_upd_no_change[where P=P, OF assms])

crunches commit_domain_time
  for obj_at[wp]: "\<lambda>s. N (obj_at P t s)"
  and kheap[wp]: "\<lambda>s. P (kheap s)"

lemma set_next_timer_interrupt_valid_sched[wp]:
  "set_next_timer_interrupt thread_time \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_next_timer_interrupt_def)

lemma set_next_interrupt_valid_sched[wp]:
  "set_next_interrupt \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: set_next_interrupt_def wp: hoare_drop_imp)

context DetSchedSchedule_AI begin

crunch ct_not_in_q[wp]: finalise_cap "ct_not_in_q :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps maybeM_inv ignore: tcb_sched_action)

end

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and released_sc_tcb_at t and not_in_release_q t
      and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_defs
                      weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
                      obj_at_kh_kheap_simps set_scheduler_action_def in_queue_2_def
               split: scheduler_action.splits)
  by auto

lemma set_scheduler_action_swt_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
      and released_sc_tcb_at t and not_in_release_q t
      and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_defs
                      weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
                      obj_at_kh_kheap_simps set_scheduler_action_def in_queue_2_def
               split: scheduler_action.splits)
  by auto

lemma set_scheduler_action_cnt_valid_blocked_except:
  "\<lbrace>\<lambda>s. valid_blocked_except target s
        \<and> (\<forall>t. scheduler_action s = switch_thread t \<longrightarrow> \<not> not_queued t s) \<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>rv. valid_blocked_except target\<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  apply (fastforce simp: valid_blocked_defs simple_sched_action_def
                   split: scheduler_action.splits)
  done

lemma set_scheduler_action_swt_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
    and active_sc_tcb_at t and budget_sufficient t and budget_ready t and in_cur_domain t
    and simple_sched_action and (\<lambda>s. \<not> in_release_q t s)\<rbrace>
   set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  apply (clarsimp simp: valid_sched_wpsimps switch_in_cur_domain_2_def weak_valid_sched_action_2_def
                        in_queue_2_def released_sc_tcb_at_def)
  by (fastforce elim!: valid_blockedE')

lemma possible_switch_to_valid_sched_strong:
  "\<lbrace>\<lambda>s. if pred_map bound (tcb_scps_of s) target \<and> not_in_release_q target s
        then valid_sched_except_blocked s \<and> valid_blocked_except target s
              \<and> pred_map runnable (tcb_sts_of s) target \<and> target \<noteq> idle_thread s
              \<and> released_sc_tcb_at target s
        else valid_sched s\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (simp only: fun_app_def pred_tcb_at_eq_commute)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac "sc_opt = None \<or> inq"; clarsimp)
   apply (wpsimp, fastforce simp: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (wpsimp wp: set_scheduler_action_swt_valid_sched'
                    tcb_sched_enqueue_valid_sched reschedule_valid_sched_except_blocked_const
                    reschedule_required_valid_blocked thread_get_wp')
  by (auto simp: obj_at_kh_kheap_simps valid_sched_valid_sched_except_blocked vs_all_heap_simps
                 in_cur_domain_def etcb_at_def valid_sched_def not_cur_thread_def ct_in_cur_domain_def)

crunch etcb_at[wp]: awaken "etcb_at P t"
  (wp: hoare_drop_imps mapM_x_wp')

crunches awaken
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  and valid_idle[wp]: valid_idle
  and in_cur_domain[wp]: "in_cur_domain t"
  (wp: hoare_drop_imps mapM_x_wp')

(* FIXME RT: replace possible_switch_to_valid_ready_qs with this. *)
lemma possible_switch_to_valid_ready_qs'':
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> pred_map runnable (tcb_sts_of s) target \<and> released_if_bound_sc_tcb_at target s\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp simp: possible_switch_to_def obj_at_kh_kheap_simps vs_all_heap_simps
               wp: thread_get_wp' get_tcb_obj_ref_wp)

lemma possible_switch_to_valid_ready_qs:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable target and
    ((bound_sc_tcb_at (\<lambda>sc. sc = None) target) or
     (active_sc_tcb_at target and budget_ready target and budget_sufficient target))\<rbrace>
    possible_switch_to target \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_ready_qs'')
  by (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)

lemma possible_switch_to_valid_ready_qs':
  "\<lbrace>valid_ready_qs
    and (\<lambda>s. \<forall>tcb. ko_at (TCB tcb) target s \<and>
      tcb_domain tcb \<noteq> cur_domain s \<or>
      (tcb_domain tcb = cur_domain s \<and> scheduler_action s \<noteq> resume_cur_thread)
       \<longrightarrow> (runnable (tcb_state tcb) \<and> released_sc_tcb_at target s))\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
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

\<comment> \<open>set_simple_ko functions\<close>

lemma set_endpoint_idle_valid_sched_pred[wp]:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) ((ep_send_qs_of s)(ep_ptr := None))
          ((ep_recv_qs_of s)(ep_ptr := None)) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s) \<rbrace>
   set_endpoint ep_ptr IdleEP
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  by (clarsimp simp: fun_upd_def ep_at_pred_def obj_at_def vs_all_heap_simps)

lemma set_endpoint_send_valid_sched_pred[wp]:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) ((ep_send_qs_of s)(ep_ptr := Some queue))
          ((ep_recv_qs_of s)(ep_ptr := None)) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s) \<rbrace>
   set_endpoint ep_ptr (SendEP queue)
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  by (clarsimp simp: fun_upd_def ep_at_pred_def obj_at_def vs_all_heap_simps)

lemma set_endpoint_recv_valid_sched_pred[wp]:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) ((ep_send_qs_of s)(ep_ptr := None))
          ((ep_recv_qs_of s)(ep_ptr := Some queue)) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s) \<rbrace>
   set_endpoint ep_ptr (RecvEP queue)
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  by (clarsimp simp: fun_upd_def ep_at_pred_def obj_at_def vs_all_heap_simps)

lemma set_notification_valid_sched_pred[wp]:
  "set_notification ntfn_ptr ntfn \<lbrace>valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps a_type_def
          split: option.splits kernel_object.splits if_splits)

lemma set_replies_valid_sched_pred[wp]:
  "set_reply reply_ptr reply \<lbrace>valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps a_type_def
          split: option.splits kernel_object.splits if_splits)

lemma set_reply_obj_ref_valid_sched_pred[wp]:
  "set_reply_obj_ref update ref new \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def wp: set_object_wp get_object_wp)

lemma set_notification_obj_ref_valid_sched_pred[wp]:
  "set_ntfn_obj_ref update ref new \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def wp: set_object_wp get_object_wp)

lemma set_simple_ko_valid_sched_pred[wp]:
  "set_simple_ko f ptr ep
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp_strong get_object_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps a_type_def
          split: option.splits kernel_object.splits if_splits)

lemma possible_switch_to_weak_valid_sched_action[wp]:
  "\<lbrace>\<lambda>s. weak_valid_sched_action s
        \<and> (pred_map bound (tcb_scps_of s) target \<and> not_in_release_q target s
            \<longrightarrow> pred_map runnable (tcb_sts_of s) target \<and> released_sc_tcb_at target s)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: possible_switch_to_wp)
  by (clarsimp simp: weak_valid_sched_action_def vs_all_heap_simps in_release_q_def)

lemma possible_switch_to_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (wpsimp simp: possible_switch_to_def
               wp: set_scheduler_action_wp thread_get_wp' get_tcb_obj_ref_wp)

lemma possible_switch_to_activatable_ct[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace> possible_switch_to target \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp)

lemma reschedule_required_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> reschedule_required \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma possible_switch_to_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (wpsimp simp: possible_switch_to_def
                  wp: set_scheduler_action_wp thread_get_wp' get_tcb_obj_ref_wp)
  by (clarsimp simp: switch_in_cur_domain_def obj_at_kh_kheap_simps vs_all_heap_simps
                     in_cur_domain_def etcb_at_def)

lemma possible_switch_to_valid_sched_action[wp]:
  "\<lbrace>\<lambda>s. valid_sched_action s
        \<and> (pred_map bound (tcb_scps_of s) target \<and> not_in_release_q target s
            \<longrightarrow> pred_map runnable (tcb_sts_of s) target \<and> released_sc_tcb_at target s)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def)

lemma reply_unlink_sc_valid_sched_misc[wp]:
  "reply_unlink_sc sc_ptr reply_ptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def
                  wp: update_sk_obj_ref_wps set_simple_ko_wps get_simple_ko_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps pred_map_simps fun_upd_def)

lemma reply_unlink_tcb_valid_sched_pred_lift:
  assumes "\<lbrace>\<lambda>s::'z::state_ext state. valid_sched_pred_strong P' s\<rbrace>
           set_thread_state t Inactive
           \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  shows "\<lbrace>\<lambda>s::'z::state_ext state.
               pred_map (\<lambda>st. st = BlockedOnReply r \<or> (\<exists>ep pl. st = BlockedOnReceive ep (Some r) pl)) (tcb_sts_of s) t
               \<longrightarrow> valid_sched_pred_strong P' s\<rbrace>
         reply_unlink_tcb t r
         \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: assms gts_wp' get_simple_ko_wp
           simp: reply_unlink_tcb_def obj_at_kh_kheap_simps vs_all_heap_simps)

lemma reply_unlink_tcb_valid_sched_pred[valid_sched_wp]:
  "\<lbrace>\<lambda>s. pred_map (\<lambda>st. st = BlockedOnReply r \<or> (\<exists>ep pl. st = BlockedOnReceive ep (Some r) pl)) (tcb_sts_of s) t \<longrightarrow>
        P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
          (if t = cur_thread s \<and> scheduler_action s = resume_cur_thread then choose_new_thread else scheduler_action s)
          (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s(t \<mapsto> Inactive)) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  apply (rule reply_unlink_tcb_valid_sched_pred_lift)
  by (wpsimp wp: set_thread_state_valid_sched_pred_strong)

lemma reply_unlink_tcb_valid_sched_misc[wp]:
  "reply_unlink_tcb t r
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (sc_replies_of s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (last_machine_time_of s)(etcbs_of s) (tcb_scps_of s)
          (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_valid_sched_pred)

lemma valid_sched_scheduler_act_not:
  "valid_sched s \<Longrightarrow> st_tcb_at ((=) k) y s \<Longrightarrow> \<not> runnable k \<Longrightarrow> scheduler_act_not y s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                     scheduler_act_not_def obj_at_kh_kheap_simps vs_all_heap_simps)

lemma valid_sched_scheduler_act_not_better:
  "valid_sched s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) y s \<Longrightarrow> scheduler_act_not y s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                     scheduler_act_not_def obj_at_kh_kheap_simps vs_all_heap_simps)

lemma reply_unlink_tcb_valid_sched:
  "reply_unlink_tcb t rptr \<lbrace>valid_sched\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_sched_pred_lift[OF set_thread_state_Inactive_not_runnable_valid_sched])
  by (auto simp: vs_all_heap_simps valid_sched_valid_sched_except_blocked)

lemma reply_unlink_tcb_valid_release_q:
  "reply_unlink_tcb t rptr \<lbrace>valid_release_q\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_sched_pred_lift set_thread_state_not_runnable_valid_release_q)
  by (auto simp: vs_all_heap_simps)

lemma reply_unlink_tcb_valid_ready_qs:
  "reply_unlink_tcb t rptr \<lbrace>valid_ready_qs\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_ready_qs gts_wp get_simple_ko_wp
                    update_sk_obj_ref_lift)
  apply (intro conjI impI; clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_eq_commute elim!: st_tcb_weakenE)
  done

lemma reply_unlink_tcb_valid_sched_action:
  "reply_unlink_tcb t rptr \<lbrace>valid_sched_action\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_sched_pred_lift[OF set_thread_state_valid_sched_action[simplified pred_conj_def]])
  by (auto simp: valid_sched_action_def weak_valid_sched_action_def scheduler_act_not_def vs_all_heap_simps)

lemma reply_unlink_tcb_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_sched_pred_lift[OF set_thread_state_weak_valid_sched_action[simplified pred_conj_def]])
  by (auto simp: valid_sched_action_def weak_valid_sched_action_def scheduler_act_not_def vs_all_heap_simps)

lemma reply_unlink_tcb_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: gts_wp get_simple_ko_wp update_sk_obj_ref_lift)
  done

lemma reply_unlink_tcb_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_sched_pred_lift[OF set_thread_state_Inactive_not_runnable_valid_sched_except_blocked])
  by (auto simp: vs_all_heap_simps)

lemma reply_unlink_tcb_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S \<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_valid_blocked_const gts_wp get_simple_ko_wp update_sk_obj_ref_lift)
  done

lemma get_tcb_NoneD: "get_tcb t s = None \<Longrightarrow> \<not> (\<exists>v. kheap s t = Some (TCB v))"
  apply (case_tac "kheap s t", simp_all add: get_tcb_def)
  apply (case_tac a, simp_all)
  done

lemma update_sk_obj_ref_valid_sched_misc[wp]:
  "update_sk_obj_ref C f ref new
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s)
           (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
           (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
           (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
           (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_scheduler_action_swt_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except_set (insert t X) and st_tcb_at runnable t
     and budget_ready t and budget_sufficient t
     and active_sc_tcb_at t and in_cur_domain t and simple_sched_action and (\<lambda>s. \<not> in_release_q t s)\<rbrace>
   set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_ s. valid_sched_except_blocked s \<and> valid_blocked_except_set X s \<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  by (auto simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
                 weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def
                 not_in_release_q_def switch_in_cur_domain_def valid_blocked_defs
                 simple_sched_action_def vs_all_heap_simps obj_at_kh_kheap_simps
          split: scheduler_action.splits)

\<comment> \<open>This is actually entirely equivalent to possible_switch_to_valid_sched_strong\<close>
lemma possible_switch_to_valid_sched_weak:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> valid_blocked_except target s
         \<and> (pred_map bound (tcb_scps_of s) target \<and> not_in_release_q target s
             \<longrightarrow> pred_map runnable (tcb_sts_of s) target \<and> released_sc_tcb_at target s
                 \<and> target \<noteq> idle_thread s)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_sched_strong simp: valid_sched_def valid_blocked_defs)
  apply (case_tac "t=target", clarsimp simp: vs_all_heap_simps)
  by fastforce

lemma possible_switch_to_valid_blocked:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert target S) s\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>rv s. valid_blocked_except_set S s\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac "sc_opt = None \<or> inq"; clarsimp)
   apply (wpsimp, fastforce simp: valid_blocked_defs obj_at_kh_kheap_simps vs_all_heap_simps)
  apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set reschedule_required_valid_blocked
                    set_scheduler_action_valid_blocked_remove thread_get_wp')
  by (auto elim!: valid_blockedE')

lemma reply_unlink_tcb_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t'\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. scheduler_act_not t'\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: gts_wp get_simple_ko_wp)

lemma set_thread_state_pred_map_tcb_sts_of:
  "\<lbrace>\<lambda>s. (t' = t \<longrightarrow> N (P st)) \<and> (t' \<noteq> t \<longrightarrow> N (pred_map P (tcb_sts_of s) t'))\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv s. N (pred_map P (tcb_sts_of s) t')\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: vs_all_heap_simps)

lemma set_thread_state_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t
    and (\<lambda>s. \<not> runnable st \<longrightarrow> not_queued t s \<and> not_in_release_q t s \<and> scheduler_act_not t s)
    and (\<lambda>s. runnable st \<longrightarrow> active_sc_tcb_at t s
           \<longrightarrow> (in_ready_q t s \<or> in_release_q t s \<or> t = cur_thread s
               \<or> scheduler_action s = switch_thread t))
    and (\<lambda>s. (is_blocked_on_recv_ntfn st \<longrightarrow> released_if_bound_sc_tcb_at t s)
             \<and> (is_blocked_on_send st \<longrightarrow> valid_sender_sc_tcb_at t s)
             \<and> (is_blocked_on_reply st \<longrightarrow> active_if_bound_sc_tcb_at t s))\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: hoare_drop_imp set_thread_state_valid_ready_qs set_thread_state_valid_release_q
                   set_thread_state_valid_sched_action set_thread_state_valid_blocked
                   set_thread_state_released_ipc_queues)

lemma restart_thread_if_no_fault_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s
        \<and> not_queued t s \<and> not_in_release_q t s \<and> scheduler_act_not t s \<and> t \<noteq> idle_thread s
        \<and> (fault_tcb_at' bound t s \<or> released_if_bound_sc_tcb_at t s)\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  supply if_split [split del]
  unfolding restart_thread_if_no_fault_def
  apply (wpsimp wp: possible_switch_to_valid_sched_strong hoare_vcg_if_lift2 hoare_vcg_imp_lift'
                    set_thread_state_valid_sched_except_blocked set_thread_state_valid_blocked
                    set_thread_state_pred_map_tcb_sts_of set_thread_state_valid_sched
                    thread_get_wp')
  apply (clarsimp simp: valid_sched_valid_sched_except_blocked[THEN iffD1]
                        obj_at_def)
  by (clarsimp simp: vs_all_heap_simps)

lemma restart_thread_if_no_fault_valid_sched_not_runnable:
  "\<lbrace>\<lambda>s. valid_sched s \<and> \<not> pred_map runnable (tcb_sts_of s) t  \<and> t \<noteq> idle_thread s
        \<and> (fault_tcb_at' bound t s \<or> released_if_bound_sc_tcb_at t s)\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: restart_thread_if_no_fault_valid_sched)
  by (clarsimp simp: valid_sched_not_runnable_not_queued valid_sched_not_runnable_not_in_release_q
                     valid_sched_not_runnable_scheduler_act_not)

lemma st_tcb_at_inactive_runnable:
  "st_tcb_at ((=) Inactive) t s \<Longrightarrow> st_tcb_at (not runnable) t s "
  by (clarsimp elim!: st_tcb_weakenE simp: pred_neg_def)

lemma reply_unlink_tcb_not_runnable[wp]:
  "\<lbrace>\<top>\<rbrace>
     reply_unlink_tcb t r
   \<lbrace>\<lambda>rv. st_tcb_at (not runnable) t\<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_inactive
         | strengthen st_tcb_at_inactive_runnable)+

lemma ipc_queued_thread_state_not_runnable:
  "ipc_queued_thread_state st \<Longrightarrow> \<not> runnable st"
  by (cases st; simp add: ipc_queued_thread_state_def)

lemma pred_map_weakenE:
  assumes "pred_map P m x"
  assumes "\<And>y. P y \<Longrightarrow> Q y"
  shows "pred_map Q m x"
  using assms by (auto simp: pred_map_simps)

lemma cancel_all_ipc_loop_body_valid_sched:
  "\<lbrace>(\<lambda>s. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s) and valid_sched\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt _ \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        y <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: restart_thread_if_no_fault_valid_sched reply_unlink_tcb_valid_sched
                    reply_unlink_tcb_valid_sched_pred_lift[OF set_thread_state_pred_map_tcb_sts_of]
                    gts_wp')
  apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) t", fastforce simp: vs_all_heap_simps is_blocked_thread_state_defs)
  apply (clarsimp simp: valid_sched_not_runnable_not_queued valid_sched_not_runnable_not_in_release_q
                        valid_sched_not_runnable_scheduler_act_not)
  apply (frule valid_sched_released_ipc_queues, simp add: released_ipc_queues_defs)
  apply (drule_tac x=t in spec)
  by (intro conjI; clarsimp simp: is_timeout_fault_opt_def vs_all_heap_simps)

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

lemma cancel_all_ipc_loop_body_blocked_on_send_recv:
  "\<lbrace>\<lambda>s. blocked_on_send_recv_tcb_at t' s \<and> t' \<noteq> t\<rbrace>
     do st <- get_thread_state t;
        reply_opt <- case st of BlockedOnReceive x r_opt _ \<Rightarrow> return r_opt | _ \<Rightarrow> return None;
        _ <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb t (the reply_opt));
        restart_thread_if_no_fault t
     od
  \<lbrace>\<lambda>_. blocked_on_send_recv_tcb_at t'\<rbrace>"
  by (wpsimp wp: restart_thread_if_no_fault_other[unfolded obj_at_kh_kheap_simps]
                 reply_unlink_tcb_st_tcb_at[unfolded obj_at_kh_kheap_simps]
                 gts_wp')

(* fixme move *)
lemma TCBBlockedRecv_in_state_refs_of:
  assumes "(ep, TCBBlockedRecv) \<in> state_refs_of s t"
  shows "\<exists>data pl. st_tcb_at ((=) (BlockedOnReceive ep data pl)) t s"
  using assms
  by (clarsimp simp: state_refs_of_def refs_of_def get_refs_def2 tcb_st_refs_of_def
                     pred_tcb_at_def obj_at_def
              split: option.splits kernel_object.splits thread_state.splits if_splits)

(* fixme move *)
lemma TCBSignal_in_state_refs_of:
  assumes "(ep, TCBSignal) \<in> state_refs_of s t"
  shows "st_tcb_at ((=) (BlockedOnNotification ep)) t s"
  using assms
  by (clarsimp simp: state_refs_of_def refs_of_def get_refs_def2 tcb_st_refs_of_def
                     pred_tcb_at_def obj_at_def
              split: option.splits kernel_object.splits thread_state.splits if_splits)

(* not used? *)
lemma pred_map_eq_pred_mapE:
 "pred_map_eq x h t
  \<Longrightarrow> P x
  \<Longrightarrow> pred_map P h t"
  unfolding pred_map_def pred_map_eq_def
  by simp

lemma ipc_queued_thread_in_ep_queueE:
  "sym_refs (state_refs_of s)
   \<Longrightarrow> ep_at_pred (\<lambda>ep. ep_queue_of ep \<noteq> None \<and> t \<in> set (the (ep_queue_of ep))) epptr s
   \<Longrightarrow> ipc_queued_thread t s"
  apply (clarsimp simp: ep_at_pred_def)
  apply (case_tac obj; simp add: ep_queue_of_def)
   apply (subgoal_tac "(epptr, TCBBlockedSend) \<in> (state_refs_of s) t")
    apply (drule TCBBlockedSend_in_state_refs_of)
    apply (clarsimp simp: tcb_at_kh_simps pred_map_simps ipc_queued_thread_state_def)
   apply (erule sym_refsE, clarsimp simp: state_refs_of_def)
  apply (subgoal_tac "(epptr, TCBBlockedRecv) \<in> (state_refs_of s) t")
   apply (drule TCBBlockedRecv_in_state_refs_of)
   apply (clarsimp simp: tcb_at_kh_simps pred_map_simps ipc_queued_thread_state_def)
   apply (erule sym_refsE, clarsimp simp: state_refs_of_def)
  done

lemma ipc_queued_thread_not_idle_thread:
  "ipc_queued_thread t s \<Longrightarrow> valid_idle s \<Longrightarrow> t \<noteq> idle_thread s"
  apply clarsimp
  apply (drule (1) st_tcb_at_idle_thread[simplified tcb_at_kh_simps])
  by (clarsimp simp: ipc_queued_thread_state_def)

lemma cancel_all_ipc_loop_valid_sched:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. blocked_on_send_recv_tcb_at t s \<and> t \<noteq> idle_thread s) and valid_sched and K (distinct queue)\<rbrace>
   mapM_x (\<lambda>t. do st <- get_thread_state t;
                  reply_opt <- case st of BlockedOnReceive _ ro _ \<Rightarrow> return ro | _ \<Rightarrow> return None;
                  _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb t (the reply_opt));
                  restart_thread_if_no_fault t
               od) queue
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_mapM_x_scheme[OF _ cancel_all_ipc_loop_body_valid_sched])
  by (wpsimp wp: cancel_all_ipc_loop_body_blocked_on_send_recv gts_wp')

(* Can this be made more general? *)
lemma case_IdleEP_helper:
  "(case x of IdleEP \<Rightarrow> f | _ \<Rightarrow> g) = (if x=IdleEP then f else g)"
  by (case_tac x; simp)

lemma cancel_all_ipc_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> valid_objs s \<and> valid_idle s \<and> sym_refs (state_refs_of s)\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding cancel_all_ipc_def case_IdleEP_helper
  apply (wpsimp wp: reschedule_valid_sched_const cancel_all_ipc_loop_valid_sched
                    get_simple_ko_wp get_ep_queue_wp'
              simp: obj_at_def)
  apply (erule (1) pspace_valid_objsE
         ; clarsimp simp: valid_obj_def valid_ep_distinct_queue pred_map_P_not_idle cong: conj_cong)
  apply (rename_tac ep q t)
  apply (case_tac ep
         ; clarsimp simp: ep_queue_of_def valid_ep_def
         ; drule (1) bspec
         ; clarsimp simp: vs_all_heap_simps obj_at_def is_tcb)
   apply (drule_tac y=t and x=epptr and tp=TCBBlockedSend in sym_refsE
          ; clarsimp simp: in_state_refs_of_iff in_get_refs in_tcb_st_refs_of_iff)
  apply (drule_tac y=t and x=epptr and tp=TCBBlockedRecv in sym_refsE
         ; clarsimp simp: in_state_refs_of_iff in_get_refs in_tcb_st_refs_of_iff)
  done

lemma set_thread_state_possible_switch_to_valid_sched_strong:
  "\<lbrace>\<lambda>s. valid_ready_qs s
        \<and> valid_release_q s
        \<and> ready_or_release s
        \<and> ct_not_in_q s
        \<and> valid_sched_action s
        \<and> ct_in_cur_domain s
        \<and> valid_blocked_except t s
        \<and> valid_idle_etcb s
        \<and> released_ipc_queues_2 (cur_time s) (tcb_sts_of s(t \<mapsto> st)) (tcb_scps_of s) (tcb_faults_of s)
                                   (sc_refill_cfgs_of s)
        \<and> active_reply_scs s
        \<and> valid_machine_time s
        \<and> active_sc_valid_refills s
        \<and> released_if_bound_sc_tcb_at t s \<and> t \<noteq> idle_thread s \<and> active ts\<rbrace>
   do y <- set_thread_state t ts;
      possible_switch_to t
   od
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_sched_weak
                    set_thread_state_runnable_valid_sched_except_blocked
                    set_thread_state_valid_blocked_const[where S="{t}"]
                    hoare_vcg_imp_lift' set_thread_state_pred_map_tcb_sts_of
              simp: runnable_eq_active)
  by (intro conjI; clarsimp simp: valid_sched_def vs_all_heap_simps fun_upd_def
                           split: if_splits elim!: released_ipc_queuesE)

lemma set_thread_state_possible_switch_to_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> released_if_bound_sc_tcb_at t s \<and> t \<noteq> idle_thread s \<and> active ts\<rbrace>
   do y <- set_thread_state t ts;
      possible_switch_to t
   od
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: set_thread_state_possible_switch_to_valid_sched_strong)
  by (auto simp: valid_sched_def fun_upd_def vs_all_heap_simps split: if_splits elim!: released_ipc_queuesE)

lemma cancel_all_signals_loop_valid_sched:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. blocked_on_recv_ntfn_tcb_at t s \<and> t \<noteq> idle_thread s) and valid_sched and K (distinct queue)\<rbrace>
       mapM_x (\<lambda>t.
             do y <- set_thread_state t Restart;
                possible_switch_to t
             od) queue
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_mapM_x_scheme)
    apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of set_thread_state_possible_switch_to_valid_sched)+
   apply (frule valid_sched_released_ipc_queues)
   by (auto simp: released_ipc_queues_defs)

lemma cancel_all_signals_valid_sched[wp]:
  "\<lbrace>\<lambda>s. valid_sched s \<and> valid_objs s \<and>  valid_idle s \<and> sym_refs (state_refs_of s)\<rbrace>
   cancel_all_signals ntfnptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (wpsimp wp: reschedule_valid_sched_const cancel_all_signals_loop_valid_sched get_simple_ko_wp
              simp: cancel_all_signals_def obj_at_def)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_distinct_queue pred_map_P_not_idle cong: conj_cong)
  apply (rename_tac q t)
  by (drule_tac x=ntfnptr and y=t and tp=TCBSignal in sym_refsE
      ; clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)

crunches thread_set
  for ready_queues[wp]:  "\<lambda>s. P (ready_queues s)"
  and release_queue'[wp]:  "\<lambda>s. P (release_queue s)"
  and cur_domain'[wp]:  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps)

lemma thread_set_etcbs:
  "\<lbrakk>\<And>x. tcb_priority (f x) = tcb_priority x; \<And>x. tcb_domain (f x) = tcb_domain x\<rbrakk> \<Longrightarrow>
  thread_set f tptr \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  by (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def)

lemmas thread_set_active_sc_tcb_at = bound_sc_obj_tcb_at_thread_set_no_change[where P=active_scrc]

lemma thread_set_valid_ready_qs:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_priority (f x) = tcb_priority x;
    \<And>x. tcb_domain (f x) = tcb_domain x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
    \<lbrace>valid_ready_qs\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (rule valid_ready_qs_lift;
      wpsimp wp: thread_set_no_change_tcb_state[unfolded obj_at_kh_kheap_simps]
                 thread_set_etcbs thread_set_active_sc_tcb_at
                 budget_ready_thread_set_no_change budget_sufficient_thread_set_no_change)

lemma thread_set_valid_release_q:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_release_q\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def)

lemma thread_set_weak_valid_sched_action:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def)

lemma thread_set_not_state_valid_sched:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   (\<And>x. tcb_fault (f x) = tcb_fault x) \<Longrightarrow>
   (\<And>x. tcb_priority (f x) = tcb_priority x) \<Longrightarrow>
   (\<And>x. tcb_domain (f x) = tcb_domain x) \<Longrightarrow>
   thread_set f tptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: thread_set_wp simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def)

lemma unbind_notification_valid_sched[wp]:
  "unbind_notification ntfnptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp simp: unbind_notification_def wp: get_tcb_obj_ref_wp)

lemma sched_context_unbind_tcb_valid_sched_misc[wp]:
  "sched_context_unbind_tcb sc_ptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s)(idle_thread s) (last_machine_time_of s) (etcbs_of s)
          (tcb_sts_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def
               wp: hoare_drop_imp hoare_vcg_all_lift set_tcb_sched_context_valid_sched_except_tcb_scp_heap)

lemma unbind_from_sc_valid_sched_misc[wp]:
  "unbind_from_sc tcb_ptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (last_machine_time_of s) (etcbs_of s)
          (tcb_sts_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp simp: unbind_from_sc_def wp: hoare_drop_imp hoare_vcg_all_lift)

crunches test_reschedule
  for valid_ready_qs[wp]: "valid_ready_qs"
  and valid_sched: "valid_sched"
  and is_sc_active[wp]: "\<lambda>s. P (is_sc_active p s)"
  (wp: hoare_drop_imps hoare_vcg_if_lift2 reschedule_valid_sched_const)

crunches tcb_release_remove
  for is_sc_active[wp]: "is_sc_active p"
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

lemma test_reschedule_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued t s \<and> (thread \<noteq> cur_thread s \<and> thread \<noteq> t \<or> scheduler_act_not t s)\<rbrace>
   test_reschedule thread
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (wpsimp wp: valid_sched_wp) (auto simp: in_queues_2_def tcb_sched_enqueue_def scheduler_act_not_def)

global_interpretation set_tcb_queue: non_heap_op "set_tcb_queue d prio queue"
  by unfold_locales (wpsimp wp: set_tcb_queue_wp)

lemma sc_tcb_sc_at_set_tcb_queue_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> tp \<notin> set queue) t s\<rbrace>
   set_tcb_queue d prio queue
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace>"
  by (wpsimp wp: set_tcb_queue_wp simp: sc_tcb_sc_at_def obj_at_def in_queues_2_def)

lemma sc_tcb_sc_at_set_scheduler_actione_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace>
   set_scheduler_action f
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  by (wpsimp simp: set_scheduler_action_def)

lemma sc_tcb_sc_at_tcb_sched_enqueue_not_queued:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s \<and> tp \<noteq> t') t s\<rbrace>
   tcb_sched_action tcb_sched_enqueue t'
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> not_queued tp s) t s\<rbrace> "
  by (wpsimp wp: tcb_sched_action_wp
           simp: sc_tcb_sc_at_def obj_at_def in_queues_2_def tcb_sched_enqueue_def)

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

lemma set_tcb_sched_context_set[wp]:
  "\<lbrace>\<lambda>s. t' = t \<or> pred_map_eq v (tcb_scps_of s) t'\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t v
   \<lbrace>\<lambda>rv s. pred_map_eq v (tcb_scps_of s) t'\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: vs_all_heap_simps)

\<comment> \<open>sched_context_donate should never be called on a thread that is already queued to run,
    i.e. in either the ready or release queues, or the target of the scheduler_action.
    However, we only need a subset of those preconditions for this lemma.\<close>
lemma sched_context_donate_valid_ready_qs':
  "\<lbrace>valid_ready_qs and not_queued tptr and scheduler_act_not tptr\<rbrace>
   sched_context_donate scptr tptr
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                 tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                 tcb_dequeue_not_queued_gen[where tptr=tptr]
                 get_sc_obj_ref_wp
           simp: sched_context_donate_def)

\<comment> \<open>might be more useful in practice\<close>
lemma sched_context_donate_valid_ready_qs[wp]:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> pred_map_eq None (tcb_scps_of s) tptr \<and> scheduler_act_not tptr s\<rbrace>
   sched_context_donate scptr tptr
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (wpsimp wp: sched_context_donate_valid_ready_qs' simp: valid_ready_qs_no_sc_not_queued)

lemma sched_context_donate_valid_release_q[wp]:
  "\<lbrace>valid_release_q and not_in_release_q tptr\<rbrace>
   sched_context_donate scptr tptr
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_release_q_not_queued
                 tcb_release_remove_not_in_release_q[where t=tptr]
           simp: sched_context_donate_def)

lemma sched_context_donate_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp wp: tcb_dequeue_not_queued_gen get_sc_obj_ref_wp
           simp: sched_context_donate_def)

lemma test_reschedule_sched_act_not_other:
  "test_reschedule t' \<lbrace>scheduler_act_not t\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

lemma test_reschedule_sched_act_not_same[wp]:
  "\<lbrace>\<top>\<rbrace> test_reschedule t \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: scheduler_act_not_def)

(* FIXME RT: brutal proof *)
lemma sched_context_donate_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp update_sched_context_wp test_reschedule_wp
                    tcb_sched_action_wp get_sc_obj_ref_wp
              simp: sched_context_donate_def tcb_release_remove_def)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def pred_map_simps tcb_sched_dequeue_def scheduler_act_not_def
                 valid_sched_action_def weak_valid_sched_action_def opt_map_simps map_join_simps
           cong: conj_cong)

lemma test_reschedule_ct_in_cur_domain[wp]:
  "test_reschedule tcb_ptr \<lbrace>ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: test_reschedule_wp)

lemma sched_context_donate_ct_in_cur_domain[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace>ct_in_cur_domain\<rbrace>"
  by (wpsimp simp: sched_context_donate_def)

lemma sorted_release_q_sc_refill_cfg_update_irrelevant:
  assumes "\<And>sc. r_time (hd (scrc_refills (f sc))) = r_time (hd (scrc_refills sc))"
  shows "sorted_release_q_2 (tcb_sc_refill_cfgs_2 tcb_scps (heap_upd f ref sc_refill_cfgs))
         = sorted_release_q_2 (tcb_sc_refill_cfgs_2 tcb_scps sc_refill_cfgs)"
  apply (rule ext, rename_tac queue, rule sorted_release_q_2_eq_lift)
  apply (intro sc_ready_time_eq_iff[THEN iffD2] conjI allI)
   apply (fastforce simp: tcb_sc_refill_cfgs_2_def opt_map_def heap_upd_def
                   split: option.splits if_splits)
  apply (rule iffI)
   apply (fastforce simp: tcb_sc_refill_cfgs_2_def sc_ready_time_def heap_upd_def
                          map_project_simps opt_map_simps map_join_simps assms
                   split: if_splits)
  apply (clarsimp simp: tcb_sc_refill_cfgs_2_def map_project_simps, rename_tac scrc scp)
  by (case_tac "scp = ref"; fastforce simp: sc_ready_time_def heap_upd_def
                                            opt_map_simps map_join_simps assms)

lemma set_sc_refill_max_valid_sched_unbound_sc:
  "\<lbrace>\<lambda>s. valid_sched s \<and> (\<nexists>t. pred_map_eq (Some ref) (tcb_scps_of s) t) \<and> \<not> non_empty_sc_replies_at ref s\<rbrace>
   set_sc_obj_ref sc_refill_max_update ref 0
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  supply if_split[split del] if_bool_simps[simp]
  apply (wpsimp wp: valid_sched_wp simp: valid_sched_def)
  apply (intro conjI)
        apply (clarsimp simp: valid_ready_queued_thread_2_def vs_all_heap_simps heap_upd_def elim!: valid_ready_qsE)
       apply (clarsimp simp: sorted_release_q_sc_refill_cfg_update_irrelevant elim!: valid_release_qE)
       apply (clarsimp simp: vs_all_heap_simps heap_upd_def)
      apply (fastforce simp: valid_sched_action_def weak_valid_sched_action_def heap_upd_def vs_all_heap_simps)
     apply (clarsimp elim!: valid_blockedE' simp: heap_upd_def vs_all_heap_simps active_sc_def split: if_splits)
    apply (fastforce simp: heap_upd_def vs_all_heap_simps is_blocked_thread_state_defs
                    elim!: released_ipc_queuesE cong: conj_cong split: if_splits)
   apply (clarsimp elim!: active_reply_scsE simp: heap_upd_def vs_all_heap_simps)
  by (clarsimp simp: active_sc_valid_refills_def heap_upd_def vs_all_heap_simps active_sc_def split: if_splits)

lemma tcb_release_remove_ready_or_release[wp]:
  "tcb_release_remove tcb_ptr \<lbrace>ready_or_release\<rbrace>"
  apply (rule hoare_pre)
  apply (rule tcb_release_remove_wp)
  apply (clarsimp simp: ready_or_release_def tcb_sched_dequeue_def ready_or_release_2_def
                        in_queue_2_def)
  done

lemma tcb_release_remove_valid_sched_not_runnable:
  "\<lbrace>\<lambda>s. valid_sched s \<and> (\<not> pred_map active (tcb_sts_of s) thread \<or> \<not> active_sc_tcb_at thread s)\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: tcb_release_remove_valid_blocked simp: valid_sched_def valid_blocked_thread_def)

lemma tcb_release_remove_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  by (wpsimp simp: valid_sched_def)

(* FIXME: not_used? *)
lemma set_mrs_ko_at_Endpoint[wp]:
  "set_mrs param_a param_b param_c \<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  apply (wpsimp simp: set_mrs_def wp: zipWithM_x_inv' set_object_wp)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

lemma reply_remove_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> reply_remove tptr rptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: hoare_vcg_if_lift2 get_tcb_obj_ref_wp get_simple_ko_wp)

crunches test_reschedule
  for valid_blocked[wp]: "valid_blocked_except_set S"
    (wp: hoare_vcg_if_lift2)

crunches reply_remove_tcb
  for not_queued[wp]: "not_queued t"
  and not_in_release_q[wp]:  "not_in_release_q t"
  (wp: crunch_wps hoare_drop_imps hoare_vcg_if_lift2 tcb_release_remove_not_in_release_q')

crunches tcb_release_remove
  for obj_at[wp]: "obj_at P p"
  (wp: crunch_wps ignore: set_object )

lemma set_tcb_queue_get_tcb[wp]:
  "set_tcb_queue d prio queue \<lbrace>\<lambda>s. P (get_tcb t s)\<rbrace> "
  by (wpsimp simp: set_tcb_queue_def get_tcb_def)

crunches test_reschedule,tcb_release_remove
  for get_tcb[wp]: "\<lambda>s. P (get_tcb t s)"
  (wp: hoare_drop_imp)

lemma sched_context_donate_active_sc_tcb_at_neq:
  "\<lbrace>active_sc_tcb_at t and K (t \<noteq> tcb_ptr) and sc_tcb_sc_at (\<lambda>tp. tp \<noteq> Some t) sc_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_pred get_sc_obj_ref_wp
              simp: sched_context_donate_def)
  by (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps sc_tcb_sc_at_def
                     pred_map_simps opt_map_simps map_join_simps
              split: if_splits)

crunches test_reschedule
  for weak_valid_sched_action[wp]: weak_valid_sched_action
  (wp: hoare_vcg_if_lift2)

lemma test_reschedule_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace>
     test_reschedule tptr \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  by (wpsimp simp: test_reschedule_def wp: reschedule_required_not_queued)

crunches tcb_release_remove
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (simp: not_in_release_q_def tcb_sched_dequeue_def)

lemma sched_context_donate_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> sched_context_donate sc_ptr tptr \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (wpsimp wp: tcb_sched_action_wp get_sc_obj_ref_wp
              simp: sched_context_donate_def)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps tcb_sched_dequeue_def in_queues_2_def
          split: if_splits)

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

lemma tcb_release_remove_in_release_q_neq:
  "\<lbrace>in_release_q t and K (t \<noteq> tptr)\<rbrace> tcb_release_remove tptr \<lbrace>\<lambda>_. in_release_q t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: in_queue_2_def tcb_sched_dequeue_def)

lemma tcb_sched_dequeue_in_ready_q_neq:
  "\<lbrace>valid_ready_qs and in_ready_q t and K (t \<noteq> tptr)\<rbrace>
   tcb_sched_action tcb_sched_dequeue tptr
   \<lbrace>\<lambda>_. in_ready_q t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_ready_qs_def in_queues_2_def tcb_sched_dequeue_def) force

lemma tcb_sched_dequeue_in_etcb_ready_q_neq:
  "\<lbrace>in_etcb_ready_q t and K (t \<noteq> tptr)\<rbrace>
   tcb_sched_action tcb_sched_dequeue tptr
   \<lbrace>\<lambda>_. in_etcb_ready_q t\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto elim!: in_etcb_ready_q_2E simp: tcb_sched_dequeue_def)

lemma sched_context_donate_in_release_queue_neq:
  "\<lbrace>in_release_q t and sc_tcb_sc_at (\<lambda>p. p \<noteq> Some t) sc_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. in_release_q t\<rbrace>"
  by (wpsimp wp: tcb_release_remove_in_release_q_neq get_sc_obj_ref_wp
           simp: sched_context_donate_def sc_tcb_sc_at_def obj_at_def)

lemma test_reschedule_in_ready_q[wp]:
  "test_reschedule t \<lbrace>in_ready_q t'\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps)

lemma test_reschedule_in_etcb_ready_q[wp]:
  "test_reschedule t \<lbrace>in_etcb_ready_q t'\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_wpsimps in_etcb_ready_q_2_def)

lemma set_tcb_sched_context_valid_blocked_Some_not_queued:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert t S) s
         \<and> (pred_map runnable (tcb_sts_of s) t \<and> is_active_sc sp s
             \<longrightarrow> t \<in> S \<or> t = cur_thread s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some sp)
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_blocked_Some')

lemma valid_blocked_thread_except:
  "t \<in> except \<Longrightarrow> valid_blocked_thread nq nr except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  by (simp add: valid_blocked_thread_def)

\<comment> \<open>When a passive server performs a ReplyRecv, it will first donate its scheduling context back
    to the previous caller during the Reply phase. If there is another caller waiting, it will
    receive another scheduling context via donating, even though it is running.
    Note that sched_context_donate is never called when t_ptr is in the ready or release queues or
    the target of switch_thread, so we don't mention those possibilities in the precondition.\<close>
lemma sched_context_donate_valid_blocked:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert t_ptr S) s
         \<and> (pred_map runnable (tcb_sts_of s) t_ptr \<and> is_active_sc scp s
             \<longrightarrow> t_ptr \<in> S \<or> t_ptr = cur_thread s)\<rbrace>
   sched_context_donate scp t_ptr
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: set_tcb_sched_context_valid_blocked_Some_not_queued
                 set_tcb_sched_context_None_valid_blocked_except_set
                 tcb_release_remove_valid_blocked
                 tcb_sched_dequeue_valid_blocked_except_set_const
                 get_sc_obj_ref_wp
           simp: valid_blocked_thread_except)

lemma released_ipc_queues_except_strengthen:
  "released_ipc_queues_2 ctime sts scps faults refill_cfgs
   \<Longrightarrow> released_ipc_queues_2 ctime (sts(tp \<mapsto> Inactive)) scps faults refill_cfgs"
  apply (erule released_ipc_queuesE)
  by (clarsimp simp: pred_map_simps ipc_queued_thread_state_def)


\<comment> \<open>When sched_context_donate is called from reply_remove, we are not always able to ensure that
    tcb_ptr satisfies released_ipc_queued_thread, but that's ok because the thread will
    subsequently be made Inactive in reply_unlink_tcb.\<close>
lemma reply_remove_sched_context_donate_released_ipc_queues:
  "\<lbrace>released_ipc_queues\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>rv s. released_ipc_queues_2 (cur_time s) (tcb_sts_of s(t \<mapsto> Inactive))
                                    (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_pred get_sc_obj_ref_wp)
  apply (intro conjI impI
         ; erule released_ipc_queuesE
         ; clarsimp simp: obj_at_def vs_all_heap_simps is_blocked_thread_state_defs
                          pred_map_simps opt_map_simps map_join_simps
                   elim!: released_ipc_queuesE split: if_splits)
  by auto

abbreviation sched_context_donate_ipc_queues_precond where
  "sched_context_donate_ipc_queues_precond t scp s
   \<equiv> (blocked_on_recv_ntfn_tcb_at t s \<longrightarrow> released_sc_at scp s)
      \<and> (blocked_on_send_tcb_at t s \<longrightarrow> (if timeout_faulted_tcb_at t s then is_active_sc scp s else released_sc_at scp s))
      \<and> (blocked_on_reply_tcb_at t s \<longrightarrow> is_active_sc scp s)"

lemma sched_context_donate_released_sc_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> sched_context_donate_ipc_queues_precond t scp s\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_pred get_sc_obj_ref_wp
              simp: sched_context_donate_def)
  by (intro conjI impI; erule released_ipc_queuesE
      ; clarsimp simp: pred_map_simps opt_map_simps map_join_simps
                split: if_splits)

lemma weak_valid_sched_action_no_sc_sched_act_not:
  "\<lbrakk>weak_valid_sched_action s; pred_map_eq None (tcb_scps_of s) ref\<rbrakk> \<Longrightarrow> scheduler_act_not ref s"
  by (auto simp: weak_valid_sched_action_def scheduler_act_not_def vs_all_heap_simps)

lemma valid_sched_action_no_sc_sched_act_not:
  "\<lbrakk>valid_sched_action s; pred_map_eq None (tcb_scps_of s) ref\<rbrakk> \<Longrightarrow> scheduler_act_not ref s"
  by (auto simp: valid_sched_action_def weak_valid_sched_action_no_sc_sched_act_not)

lemma in_ready_q_runnable:
  "valid_ready_qs_2 qs ctime etcbs sts scps scs \<Longrightarrow> in_queues_2 qs t \<longrightarrow> pred_map runnable sts t"
  by (auto simp: valid_ready_qs_def in_queues_2_def)

lemma in_release_q_runnable:
  "valid_release_q_2 q sts scps scs \<Longrightarrow> in_queue_2 q t \<longrightarrow> pred_map runnable sts t"
  by (auto simp: valid_release_q_def in_queue_2_def)

lemma switch_to_runnable:
  "valid_sched_action_2 True {} ctime sa ct cdom rlq etcbs sts scps scs \<Longrightarrow> sa = switch_thread t \<longrightarrow> pred_map runnable sts t"
  by (auto simp: valid_sched_action_def weak_valid_sched_action_def)

crunches test_reschedule
  for ready_or_release[wp]: "ready_or_release"

lemma sched_context_donate_ready_or_release[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace>ready_or_release\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: gbn_wp thread_get_wp tcb_release_remove_ready_or_release)

lemma sched_context_donate_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> pred_map_eq None (tcb_scps_of s) t
        \<and> sched_context_donate_ipc_queues_precond t scp s\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>rv. valid_sched_except_blocked\<rbrace>"
  by (wpsimp wp: sched_context_donate_valid_sched_action
                 sched_context_donate_valid_blocked
                 sched_context_donate_released_sc_released_ipc_queues
           simp: valid_sched_def
                 valid_ready_qs_no_sc_not_queued
                 valid_release_q_no_sc_not_in_release_q
                 valid_sched_action_no_sc_sched_act_not)

lemma sched_context_donate_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> pred_map_eq None (tcb_scps_of s) t
        \<and> (pred_map runnable (tcb_sts_of s) t \<and> is_active_sc scp s \<longrightarrow> t = cur_thread s)
        \<and> sched_context_donate_ipc_queues_precond t scp s\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp wp: sched_context_donate_valid_sched_except_blocked
                 sched_context_donate_valid_blocked
           simp: valid_sched_valid_sched_except_blocked)

lemma valid_sched_blocked_imp:
   "\<lbrakk>valid_sched s; not_queued t s; not_in_release_q t s; scheduler_act_not t s; t \<noteq> cur_thread s\<rbrakk> \<Longrightarrow>
             \<not> (pred_map runnable (tcb_sts_of s) t \<and> active_sc_tcb_at t s)"
  by (auto simp: valid_sched_def valid_blocked_defs scheduler_act_not_def runnable_eq_active)

lemma reschedule_cnt[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_ s. scheduler_action s = choose_new_thread\<rbrace>"
  by (wpsimp wp: valid_sched_wp)

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
  "\<lbrace>weak_valid_sched_action\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t None
   \<lbrace>\<lambda>_. weak_valid_sched_action_except t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: weak_valid_sched_action_2_def vs_all_heap_simps)

(* FIXME: move, also remove (input) and make sure print translations fire in the right order. *)
abbreviation (input) valid_sched_action_except where
  "valid_sched_action_except S s \<equiv>
    valid_sched_action_2 True S (cur_time s) (scheduler_action s) (cur_thread s) (cur_domain s)
                                (release_queue s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s)
                                (sc_refill_cfgs_of s)"

lemma test_reschedule_valid_sched_action_except:
  "\<lbrace>valid_sched_action_except (insert t S)\<rbrace> test_reschedule t \<lbrace>\<lambda>_. valid_sched_action_except S\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: valid_sched_action_2_def weak_valid_sched_action_def)

lemma test_reschedule_valid_sched_except_wk_sched_action:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked_except_wk_sched_action s
        \<and> valid_blocked s
        \<and> weak_valid_sched_action_except t s
        \<and> pred_map_eq None (tcb_scps_of s) t\<rbrace>
   test_reschedule t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp simp: valid_sched_def wp: test_reschedule_valid_sched_action_except)
  by (auto simp: valid_sched_action_def weak_valid_sched_action_def )

lemma set_tcb_sc_update_active_sc_tcb_at_None[wp]:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>rv s. \<not> (bound_sc_obj_tcb_at (P (cur_time s)) t s)\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: vs_all_heap_simps)

lemma released_ipc_queues_set_scp_None:
  assumes "released_ipc_queues_2 ctime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"
  shows "released_ipc_queues_2 ctime tcb_sts (tcb_scps(ref \<mapsto> None)) tcb_faults sc_refill_cfgs"
  apply (rule released_ipc_queuesE[OF assms])
  by (auto simp: pred_map_simps opt_map_simps map_join_simps)

lemma sched_context_donate_scheduler_act_not[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace>scheduler_act_not t\<rbrace>"
  by (wpsimp wp: test_reschedule_sched_act_not_other[where t=t] simp: sched_context_donate_def)

lemma sts_sc_tcb_sc_at_inactive:
  "\<lbrace> \<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp s \<and> inactive ts \<rbrace>
   set_thread_state t ts \<lbrace> \<lambda>rv s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp s\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
  apply (wp dxo_wp_weak set_object_wp | simp add: sc_tcb_sc_at_def)+
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

lemma set_simple_ko_is_sc_active[wp]:
  "set_simple_ko f p new \<lbrace>\<lambda>s. P (is_sc_active t s)\<rbrace>"
  apply (clarsimp simp: set_simple_ko_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp split: option.splits)
  by (intro conjI impI; clarsimp elim!: rsubst[where P=P] split: if_splits kernel_object.splits
                                    simp: a_type_def partial_inv_def obj_at_def is_sc_active_def)

crunches set_thread_state_act, update_sk_obj_ref, get_sk_obj_ref
  for is_sc_active[wp]: "\<lambda>s. P (is_sc_active t s)"
  (simp: set_scheduler_action_def)

lemma set_thread_state_is_sc_active[wp]:
  "set_thread_state st tp \<lbrace>\<lambda>s. P (is_sc_active t s)\<rbrace>"
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp simp: is_sc_active_def dest!: get_tcb_SomeD)

lemma reply_unlink_sc_is_sc_active[wp]:
  "reply_unlink_sc sp rp \<lbrace>\<lambda>s. P (is_sc_active t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_sc_def)

lemma reply_unlink_tcb_is_sc_active[wp]:
  "reply_unlink_tcb tp rp \<lbrace>\<lambda>s. P (is_sc_active t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_tcb_def)

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
  apply (simp add: set_thread_state_def)
  apply (wp set_object_wp|simp)+
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

text \<open>The reply a TCB is waiting on\<close>
definition
  reply_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "reply_blocked ts \<equiv> case ts of
     BlockedOnReceive ep (Some r) _ \<Rightarrow> Some r
   | BlockedOnReply r \<Rightarrow> Some r
   | _ \<Rightarrow> None"

(* FIXME: unused
lemma reply_remove_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))
    and (\<lambda>s. reply_sc_reply_at (\<lambda>p. \<forall>scp. p = Some scp
             \<longrightarrow> sc_tcb_sc_at (\<lambda>x. x \<noteq> Some t) scp s) rptr s) \<comment> \<open>callee\<close>\<rbrace>
     reply_remove tptr rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
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
                      sc_tcb_sc_at_def is_tcb is_reply sc_at_ppred_def
               dest!: sc_with_reply_SomeD
                      sym_refs_reply_sc_reply_at[where reply_ptr=rptr and sc_ptr=sc_ptr
                                                   and list="tl (sc_replies sc)"]
              intro!: hd_Cons_tl)
    done .
*)


lemma set_tcb_obj_ref_reply_at_ppred:
  assumes "\<And>P. set_tcb_obj_ref f t v \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "set_tcb_obj_ref f t v \<lbrace>\<lambda>s. reply_at_ppred proj (P (g s)) rp s\<rbrace>"
  apply (rule hoare_lift_Pf[where f=g, OF _ assms])
  by (wpsimp wp: set_tcb_obj_ref_wp simp: reply_at_ppred_def obj_at_def)

lemmas set_tcb_obj_ref_reply_at_ppred_sched_act[wp]
  = set_tcb_obj_ref_reply_at_ppred[where g=scheduler_action, OF set_tcb_obj_ref_scheduler_action]

lemma update_sched_context_reply_at_ppred:
  assumes "\<And>P. update_sched_context sp f \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "update_sched_context sp f \<lbrace>\<lambda>s. reply_at_ppred proj (P (g s)) rp s\<rbrace>"
  apply (rule hoare_lift_Pf[where f=g, OF _ assms])
  by (wpsimp wp: update_sched_context_wp simp: reply_at_ppred_def obj_at_def)

lemmas update_sched_context_reply_at_ppred_sched_act[wp]
  = update_sched_context_reply_at_ppred[where g=scheduler_action, OF update_sched_context_valid_sched_misc]

crunches tcb_sched_action (* why do we need this? *)
  for reply_tcb_reply_at'[wp]: "reply_tcb_reply_at P s"

lemma reschedule_reply_tcb_reply_at_act_not:
  "reschedule_required \<lbrace>\<lambda>s. reply_tcb_reply_at (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s) rp s\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: reply_tcb_reply_at_def obj_at_def)

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
  "sched_context_donate scp tp \<lbrace>\<lambda>s. reply_tcb_reply_at (\<lambda>p. \<forall>t. p = Some t \<longrightarrow> scheduler_act_not t s) rp s\<rbrace>"
  by (wpsimp wp: set_tcb_queue_wp test_reschedule_reply_tcb_reply_at_act_not
                 tcb_release_remove_reply_tcb_reply_at_act_not
           simp: sched_context_donate_def get_sc_obj_ref_def tcb_sched_action_def)

lemma valid_sched_not_schedulable_sc_not_queued:
  "\<lbrakk>valid_sched s; \<not> is_schedulable_bool tptr (in_release_queue tptr s) s; tcb_at tptr s\<rbrakk>
     \<Longrightarrow> in_release_queue tptr s \<or> not_queued tptr s"
  by (fastforce simp: is_schedulable_bool_def obj_at_kh_kheap_simps vs_all_heap_simps is_tcb
                      valid_sched_def valid_ready_qs_def in_ready_q_def
               split: option.splits)

lemma reply_unlink_tcb_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues_2 (cur_time s) (tcb_sts_of s(t \<mapsto> Inactive))
                              (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>
   reply_unlink_tcb t rptr
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
   unfolding reply_unlink_tcb_def
   by (wpsimp wp: set_thread_state_valid_sched_pred hoare_drop_imps)

lemma reply_unlink_sc_active_reply_scs[wp]:
  "reply_unlink_sc sc_ptr reply_ptr \<lbrace>active_reply_scs\<rbrace>"
  unfolding reply_unlink_sc_def
  apply (rule hoare_seq_ext[OF _ gscrpls_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if
         ; (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
         ; wpsimp wp: update_sc_replies_valid_sched_pred)
  by (auto simp: obj_at_kh_kheap_simps heap_upd_def vs_all_heap_simps
          split: if_splits elim!: active_reply_scsE)

lemma reply_unlink_sc_valid_sched[wp]:
  "reply_unlink_sc sc_ptr reply_ptr \<lbrace>valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def)

lemma released_ipc_queues_update_state_trivial:
  assumes st: "\<not> ipc_queued_thread_state st"
  assumes sc: "released_ipc_queues_2 ctime sts scps faults scrcs"
  shows "released_ipc_queues_2 ctime (sts(t \<mapsto> st)) scps faults scrcs"
  using assms by (auto elim!: released_ipc_queuesE simp: pred_map_simps is_blocked_thread_state_defs split: if_splits)

lemmas released_ipc_queues_upd_Inactive[simp, elim!]
  = released_ipc_queues_update_state_trivial[where st=Inactive, simplified]

lemma reply_remove_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> ipc_queued_thread tp s\<rbrace>
   reply_remove tp rp
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  supply if_split[split del]
  apply (simp add: reply_remove_def valid_sched_def)
  apply (repeat 3 \<open>rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?\<close>)
  apply (rule_tac hoare_seq_ext
         , wpsimp wp: reply_unlink_tcb_valid_ready_qs reply_unlink_tcb_valid_release_q
                      reply_unlink_tcb_valid_sched_action reply_unlink_tcb_ct_in_cur_domain
                      reply_unlink_tcb_valid_blocked_except_set reply_unlink_tcb_released_ipc_queues)
  apply (case_tac r_sc_opt, wpsimp, clarsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_when_cases; clarsimp)
  apply (wpsimp wp: sched_context_donate_valid_sched_action sched_context_donate_valid_blocked
                    reply_remove_sched_context_donate_released_ipc_queues)
  apply (strengthen valid_sched_not_runnable_not_queued valid_sched_scheduler_act_not_better
                    valid_sched_not_runnable_not_in_release_q released_ipc_queues_except_strengthen)
  by (auto dest: ipc_queued_thread_state_not_runnable simp: valid_sched_def pred_map_simps tcb_at_kh_simps)

\<comment> \<open>The operations that make up cancel_ipc affect valid_sched_pred in similar ways.\<close>
locale set_thread_state_Inactive_valid_sched_pred_equiv =
  fixes f :: "obj_ref \<Rightarrow> ('state_ext::state_ext state, 'a) nondet_monad"
  fixes tptr :: obj_ref
  \<comment> \<open>We can't put sc_replies in here, because we want to use this locale for functions
      that modify that field.\<close>
  assumes valid_sched_pred:
    "\<And>P. \<lbrace>\<lambda>s::'state_ext state.
             P (consumed_time s) (cur_sc s) (sc_tcbs_of s)
               (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
               (if tptr = cur_thread s \<and> scheduler_action s = resume_cur_thread then choose_new_thread else scheduler_action s)
               (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s(tptr \<mapsto> Inactive)) (tcb_scps_of s)
               (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>
          f tptr
          \<lbrace>\<lambda>rv s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s)
                    (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
                    (scheduler_action s) (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s)
                    (tcb_faults_of s) (sc_refill_cfgs_of s)\<rbrace>"
  assumes non_empty_sc_replies_at[wp]:
    "\<And>scp. f tptr \<lbrace>\<lambda>s::'state_ext state. \<not> non_empty_sc_replies_at scp s\<rbrace>"

context set_thread_state_Inactive_valid_sched_pred_equiv begin

lemmas valid_sched_misc[wp]
  = valid_sched_pred[where P="\<lambda>cons csc tcbs ctime cdom ct it rq rlq _ lmt etcbs _ scps faults scrcs.
                               P cons csc tcbs ctime cdom ct it rq rlq lmt etcbs scps faults scrcs :: bool" for P]

lemma valid_ready_qs:
  "\<lbrace>\<lambda>s::'state_ext state. valid_ready_qs s \<and> \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrace>
   f tptr
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: valid_sched_pred)
  by (clarsimp simp: valid_ready_queued_thread_2_def vs_all_heap_simps
              elim!: valid_ready_qsE split: if_splits)

lemma valid_release_q:
  "\<lbrace>\<lambda>s::'state_ext state. valid_release_q s \<and> \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrace>
   f tptr
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_pred)
  by (fastforce simp: valid_release_q_def vs_all_heap_simps split: if_splits)

lemma ct_not_in_q[wp]:
  "f tptr \<lbrace>ct_not_in_q::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_pred)

lemma valid_sched_action:
  "\<lbrace>\<lambda>s::'state_ext state. valid_sched_action s \<and> \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrace>
   f tptr
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (wpsimp wp: valid_sched_pred)
  by (fastforce simp: valid_sched_action_def weak_valid_sched_action_def vs_all_heap_simps
                      is_activatable_def
               split: if_splits)

lemma ct_in_cur_domain[wp]:
  "f tptr \<lbrace>ct_in_cur_domain::'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_pred)

lemma valid_blocked_tcb_at[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. t' \<noteq> tptr \<longrightarrow> valid_blocked_tcb_at t' s\<rbrace>
   f tptr
   \<lbrace>\<lambda>_. valid_blocked_tcb_at t'\<rbrace>"
  apply (wpsimp wp: valid_sched_pred)
  by (clarsimp simp: valid_blocked_thread_def vs_all_heap_simps)

lemma valid_blocked[wp]:
  "\<lbrace>valid_blocked_except_set (insert tptr S)::'state_ext state \<Rightarrow> _\<rbrace>
   f tptr
   \<lbrace>\<lambda>_. valid_blocked_except_set S::'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (wpsimp wp: valid_sched_pred)
  by (erule valid_blockedE'; case_tac "t=tptr"; clarsimp simp: vs_all_heap_simps)

lemma active_reply_scs[wp]:
  "f tptr \<lbrace>active_reply_scs::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding active_reply_scs_defs
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

lemmas valid_sched_lemmas
  = valid_ready_qs valid_release_q valid_sched_action
    valid_sched_pred[where P="\<lambda>cons csc tcbs ctime cdom ct it rq rlq sa lmt etcbs sts scps faults scrcs.
                                released_ipc_queues_2 ctime sts scps faults scrcs"]

lemma valid_sched:
  "\<lbrace>\<lambda>s::'state_ext state.
        valid_ready_qs s
        \<and> valid_release_q s
        \<and> ready_or_release s
        \<and> ct_not_in_q s
        \<and> valid_sched_action s
        \<and> ct_in_cur_domain s
        \<and> valid_blocked_except tptr s
        \<and> valid_idle_etcb s
        \<and> released_ipc_queues_2 (cur_time s) (tcb_sts_of s(tptr \<mapsto> Inactive)) (tcb_scps_of s)
                                   (tcb_faults_of s) (sc_refill_cfgs_of s)
        \<and> active_reply_scs s
        \<and> valid_machine_time s
        \<and> active_sc_valid_refills s
        \<and> \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrace>
   f tptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_lemmas simp: valid_sched_def)

lemma valid_sched_except_blocked:
  "\<lbrace>\<lambda>s::'state_ext state.
        valid_ready_qs s
        \<and> valid_release_q s
        \<and> ready_or_release s
        \<and> ct_not_in_q s
        \<and> valid_sched_action s
        \<and> ct_in_cur_domain s
        \<and> valid_idle_etcb s
        \<and> released_ipc_queues_2 (cur_time s) (tcb_sts_of s(tptr \<mapsto> Inactive)) (tcb_scps_of s)
                                   (tcb_faults_of s) (sc_refill_cfgs_of s)
        \<and> active_reply_scs s
        \<and> valid_machine_time s
        \<and> active_sc_valid_refills s
        \<and> \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrace>
   f tptr
   \<lbrace>\<lambda>rv. valid_sched_except_blocked\<rbrace>"
  by (wpsimp wp: valid_sched_lemmas simp: valid_sched_def)

end

global_interpretation set_thread_state_Inactive:
  set_thread_state_Inactive_valid_sched_pred_equiv "\<lambda>t. set_thread_state t Inactive"
  by unfold_locales (wpsimp wp: set_thread_state_valid_sched_pred_strong simp: fun_upd_def)+

global_interpretation reply_unlink_tcb: set_thread_state_Inactive_valid_sched_pred_equiv "\<lambda>t. reply_unlink_tcb t r"
  by unfold_locales (wpsimp wp: reply_unlink_tcb_valid_sched valid_sched_wp simp: fun_upd_def)+

lemma reply_remove_tcb_non_empty_sc_replies_at[wp]:
  "reply_remove_tcb t r \<lbrace>\<lambda>s. \<not> non_empty_sc_replies_at scp s\<rbrace>"
  unfolding reply_remove_tcb_def
  apply (wpsimp wp: update_sc_replies_valid_sched_pred get_sk_obj_ref_wp gts_wp)
  by (auto simp: heap_upd_def vs_all_heap_simps)

global_interpretation reply_remove_tcb: set_thread_state_Inactive_valid_sched_pred_equiv "\<lambda>t. reply_remove_tcb t r"
  apply unfold_locales
   prefer 2 subgoal by wp
  unfolding reply_remove_tcb_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp], rule hoare_gen_asm_conj)
  apply (clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext_skip
         , solves \<open>wpsimp wp: hoare_drop_imps
                        simp: obj_at_kh_kheap_simps vs_all_heap_simps fun_upd_def\<close>)+
  by (wpsimp wp: reply_unlink_tcb_valid_sched_pred simp: fun_upd_def)

lemma unbind_maybe_notification_valid_sched[wp]:
  "unbind_maybe_notification ptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: get_sk_obj_ref_wp simp: unbind_maybe_notification_def)

global_interpretation cancel_signal: set_thread_state_Inactive_valid_sched_pred_equiv "\<lambda>t. cancel_signal t ntfn"
  apply unfold_locales
  unfolding cancel_signal_def
  supply if_split[split del]
  apply (rule hoare_seq_ext_skip, solves wpsimp, simp?)+
  by (wpsimp wp: set_thread_state_Inactive.valid_sched_pred get_simple_ko_wp simp: fun_upd_def)+

crunch st_tcb_at_not_runnable[wp]: reply_remove_tcb "st_tcb_at (\<lambda>st. \<not>runnable st) t"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps wp_del: reply_remove_st_tcb_at)

lemma reply_remove_tcb_not_runnable[wp]:
  "reply_unlink_tcb t r \<lbrace>\<lambda>s. \<not> pred_map runnable (tcb_sts_of s) t\<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_valid_sched_pred simp: vs_all_heap_simps)

global_interpretation blocked_cancel_ipc:
  set_thread_state_Inactive_valid_sched_pred_equiv "\<lambda>t. blocked_cancel_ipc st t r"
  apply unfold_locales
  unfolding blocked_cancel_ipc_def
  subgoal for P
    supply if_split[split del]
    apply (rule hoare_seq_ext_skip, solves wpsimp, simp?)+
    apply (cases r; simp add: bind_assoc; thin_tac _)
     apply (wpsimp wp: set_thread_state_valid_sched_pred_strong simp: fun_upd_def)
    apply (rule hoare_seq_ext_skip, solves wpsimp, simp?)+
    apply (wpsimp wp: set_thread_state_valid_sched_pred_strong
                      reply_unlink_tcb_valid_sched_pred_lift[THEN hoare_drop_assertion])
    apply (clarsimp simp: fun_upd_def split: if_splits)
    done
  apply (wpsimp wp: hoare_drop_imp simp: blocked_cancel_ipc_def)
  done

lemmas cancel_ipc_valid_sched_lemmas
  = reply_remove_tcb.valid_sched
    cancel_signal.valid_sched
    blocked_cancel_ipc.valid_sched

lemma get_tcb_after_put[simp]:
  "get_tcb t (kheap_update (\<lambda>kh. kh(t \<mapsto> TCB tcb)) s) = Some tcb"
  by (simp add: get_tcb_def)

crunches sched_context_unbind_yield_from
  for valid_sched[wp]: "valid_sched_pred_strong P"
  (wp: maybeM_inv mapM_x_wp')

lemma sched_context_unbind_ntfn_valid_sched[wp]:
  "sched_context_unbind_ntfn scptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: get_sc_obj_ref_wp simp: sched_context_unbind_ntfn_def)

lemma sched_context_maybe_unbind_ntfn_valid_sched[wp]:
  "sched_context_maybe_unbind_ntfn scptr \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (wpsimp wp: get_sk_obj_ref_wp simp: sched_context_maybe_unbind_ntfn_def)

(* FIXME: Move *)
lemma sym_ref_tcb_reply_Receive:
   "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_state tcb = BlockedOnReceive ep (Some rp) pl \<rbrakk> \<Longrightarrow>
  \<exists>reply. kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some tp"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def get_refs_def2 elim!: sym_refsE)
  apply (drule_tac x="(rp, TCBReply)" in bspec)
   apply fastforce
  apply (clarsimp simp: obj_at_def)
  apply (case_tac koa; clarsimp simp: get_refs_def2)
  done

lemma thread_set_fault_valid_sched_pred:
  "\<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (heap_upd f tptr (tcb_faults_of s))
          (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>
   thread_set (tcb_fault_update f) tptr
   \<lbrace>\<lambda>rv. valid_sched_pred_strong P\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  by (auto simp: heap_upd_def fun_upd_def obj_at_kh_kheap_simps vs_all_heap_simps
          elim!: rsubst[of "\<lambda>t::obj_ref \<rightharpoonup> fault option. P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _ _ :: bool"]
          split: if_splits)

lemmas thread_set_fault_valid_sched_misc[wp]
  = thread_set_fault_valid_sched_pred[where P="\<lambda>cons csc ep_send_qs ep_recv_qs tcbs ctime cdom ct it qs rq sa lmt etcbs sts scps _ scrcs reps.
                                                P cons csc ep_send_qs ep_recv_qs tcbs ctime cdom ct it qs rq sa lmt etcbs sts scps scrcs reps :: bool" for P]

lemma cancel_ipc_valid_sched[wp]:
  "cancel_ipc tptr \<lbrace>valid_sched\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule_tac B="\<lambda>rv s. pred_map_eq state (tcb_sts_of s) tptr
                            \<and> valid_ready_qs s
                            \<and> valid_release_q s
                            \<and> ready_or_release s
                            \<and> ct_not_in_q s
                            \<and> valid_sched_action s
                            \<and> ct_in_cur_domain s
                            \<and> valid_blocked s
                            \<and> valid_idle_etcb s
                            \<and> released_ipc_queues_2 (cur_time s) (tcb_sts_of s(tptr \<mapsto> Inactive)) (tcb_scps_of s)
                                                       (tcb_faults_of s) (sc_refill_cfgs_of s)
                            \<and> active_reply_scs s
                            \<and> active_sc_valid_refills s
                            \<and> valid_machine_time s" in hoare_seq_ext)
   apply (wpsimp wp: cancel_ipc_valid_sched_lemmas)
   apply (prop_tac "\<not> ipc_queued_thread_state state \<Longrightarrow> valid_sched s")
    apply (fastforce simp: valid_sched_def vs_all_heap_simps runnable_eq fun_upd_def
                           is_blocked_thread_state_defs
                    split: if_splits elim!: released_ipc_queuesE)
   apply (prop_tac "ipc_queued_thread_state state \<Longrightarrow> \<not> pred_map runnable (tcb_sts_of s) tptr")
    apply (rule ccontr; fastforce simp: vs_all_heap_simps runnable_eq)
   apply fastforce
  apply (wpsimp wp: thread_set_fault_valid_sched_pred simp: valid_sched_def)
  apply (clarsimp simp: vs_all_heap_simps is_blocked_thread_state_defs heap_upd_def
                 split: if_splits elim!: released_ipc_queuesE)
  done

lemma possible_switch_to_ct_in_cur_domain[wp]:
  "possible_switch_to target \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding possible_switch_to_def set_scheduler_action_def
  by (wpsimp wp: get_tcb_obj_ref_wp thread_get_wp')

lemma possible_switch_to_not_cur_thread[wp]:
  "possible_switch_to tptr \<lbrace>not_cur_thread t\<rbrace>"
  by (wpsimp wp: valid_sched_wp thread_get_wp' get_tcb_obj_ref_wp
           simp: possible_switch_to_def)

crunch simple[wp]: reply_remove simple_sched_action
  (simp: a_type_def wp: hoare_drop_imps)

lemma sched_context_unbind_tcb_simple_sched_action[wp]:
  "sched_context_unbind_tcb sc_ptr \<lbrace>simple_sched_action\<rbrace>"
  "sched_context_unbind_tcb sc_ptr \<lbrace>scheduler_act_sane\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)+

crunches unbind_from_sc, sched_context_unbind_all_tcbs
  for simple[wp]: simple_sched_action
  and scheduler_act_sane[wp]: scheduler_act_sane
  (wp: maybeM_wp crunch_wps hoare_vcg_all_lift)

crunch scheduler_act_not[wp]: unbind_from_sc "scheduler_act_not t"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

crunches cancel_ipc
for simple_sched_action[wp]: simple_sched_action
and scheduler_act_sane[wp]: scheduler_act_sane
and scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: maybeM_wp hoare_drop_imps)

lemma cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; wpsimp)
  done

lemma distinct_zip_snd_unique:
  "\<lbrakk>distinct xs; (a, b) \<in> set (zip xs ys); (a, b') \<in> set (zip xs ys)\<rbrakk>
     \<Longrightarrow> b = b'"
  apply (induct xs arbitrary: ys, simp)
  apply (clarsimp simp: zip_Cons1)
  apply (erule disjE, fastforce dest!: in_set_zipE)
  apply (erule disjE, fastforce dest!: in_set_zipE, clarsimp)
  done

lemma set_insort_filter_insert:
  "set (insort_filter P x xs) = insert x (set xs)"
  by (auto simp: insort_filter_def)

lemma set_tcb_release_enqueue_upd_insert:
  "set (tcb_release_enqueue_upd ready_times t queue) = insert t (set queue)"
  by (simp add: tcb_release_enqueue_upd_def set_insort_filter_insert)

lemma distinct_filter_iff:
  "distinct xs \<longleftrightarrow> distinct (filter P xs) \<and> distinct (filter (Not \<circ> P) xs)"
proof (induct xs)
  case (Cons x xs) show ?case
    apply (cases "x \<in> set xs"; simp)
    by (rule Cons[simplified comp_def])
qed auto

lemma distinct_insort_filter:
  "distinct (insort_filter P x xs) \<longleftrightarrow> x \<notin> set xs \<and> distinct xs"
  by (auto simp: insort_filter_def distinct_filter_iff[where xs=xs and P=P, simplified comp_def]
           simp del: distinct_filter)

lemma distinct_tcb_release_enqueue_upd:
  "distinct (tcb_release_enqueue_upd ready_times t queue) \<longleftrightarrow> \<not> in_queue_2 queue t \<and> distinct queue"
  by (simp add: tcb_release_enqueue_upd_def distinct_insort_filter in_queue_2_def)

lemma tcb_release_enqueue_in_release_q[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_release_enqueue tcbptr \<lbrace>\<lambda>ya. in_release_q tcbptr\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: in_queue_2_def set_tcb_release_enqueue_upd_insert)

(* FIXME move *)
lemma valid_release_q_active_sc:
  "valid_release_q s \<Longrightarrow> t \<in> set (release_queue s) \<Longrightarrow> active_sc_tcb_at t s"
  by (clarsimp simp: valid_release_q_def)

lemma insort_filter_cong:
  assumes xs: "x = y" "xs = ys"
  assumes P: "\<And>x. x \<in> set ys \<Longrightarrow> P x \<longleftrightarrow> Q x"
  shows "insort_filter P x xs = insort_filter Q y ys"
  unfolding insort_filter_def
  apply (intro arg_cong2[where f=append] arg_cong2[where f=Cons] filter_cong xs)
  by (auto simp: P)

lemma tcb_release_enqueue_upd_def2:
  assumes "\<forall>x \<in> set (t # queue). \<exists>y. hp x = Some y"
  shows "tcb_release_enqueue_upd hp t queue = insort_filter (\<lambda>t'. img_ord hp opt_ord t' t) t queue"
  using assms by (auto simp: tcb_release_enqueue_upd_def img_ord_def intro!: insort_filter_cong)

lemma sc_ready_times_2_Some:
  "hp t = Some scrc \<Longrightarrow> sc_ready_times_2 hp t = Some (sc_ready_time scrc)"
  by (simp add: sc_ready_times_2_def map_project_simps)

lemma transp_img_ord:
  "transp cmp \<Longrightarrow> transp (img_ord f cmp)"
  unfolding transp_def img_ord_def by blast

lemma transp_opt_ord:
  "transp (opt_ord :: ('a::preorder) option \<Rightarrow> 'a option \<Rightarrow> bool)"
  apply (clarsimp simp: transp_def)
  by (case_tac x; case_tac y; case_tac z; clarsimp elim!: order_trans)

lemma reflp_img_ord:
  "reflp cmp \<Longrightarrow> reflp (img_ord f cmp)"
  unfolding reflp_def img_ord_def by blast

lemma reflp_opt_ord:
  "reflp (opt_ord :: ('a::preorder) option \<Rightarrow> 'a option \<Rightarrow> bool)"
  apply (clarsimp simp: reflp_def)
  by (case_tac x; clarsimp)

lemma total_img_ord:
  "\<lbrakk>total {(x,y). cmp x y}; reflp cmp\<rbrakk> \<Longrightarrow> total {(x,y). img_ord f cmp x y}"
  apply (clarsimp simp: total_on_def reflp_def img_ord_def)
  by (drule_tac x="f x" in spec; drule_tac x="f y" in spec; fastforce)

lemma total_opt_ord:
  "total {(x :: ('a::linorder) option, y). opt_ord x y}"
  apply (clarsimp simp: total_on_def)
  apply (case_tac x; case_tac y)
  by (auto simp: linear)

lemma sorted_tcb_release_enqueue_upd:
  assumes "sorted_release_q_2 hp queue"
  assumes "\<forall>x \<in> set (t # queue). \<exists>y. hp x = Some y"
  shows "sorted_release_q_2 hp (tcb_release_enqueue_upd (sc_ready_times_2 hp) t queue)"
  using assms
  apply (clarsimp simp add: sorted_release_q_2_def)
  apply (subst tcb_release_enqueue_upd_def2, fastforce simp add: sc_ready_times_2_Some)
  by (erule sorted_insort_filter[where cmp="img_ord (sc_ready_times_2 hp) opt_ord" and xs=queue, rotated 3]
      ; intro transp_img_ord reflp_img_ord total_img_ord transp_opt_ord reflp_opt_ord total_opt_ord)

lemma tcb_release_enqueue_valid_release_q[wp]:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> active_sc_tcb_at t s \<and> pred_map runnable (tcb_sts_of s) t \<and> not_in_release_q t s\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (wpsimp wp: valid_sched_wp
              simp: valid_release_q_def set_tcb_release_enqueue_upd_insert
                    distinct_tcb_release_enqueue_upd)
  apply (erule sorted_tcb_release_enqueue_upd)
  by (auto simp: tcb_sc_refill_cfgs_2_def opt_map_simps map_join_simps vs_all_heap_simps)

lemma tcb_release_enqueue_valid_sched_action[wp]:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> scheduler_act_not thread s\<rbrace>
   tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (auto simp: valid_sched_action_def weak_valid_sched_action_def scheduler_act_not_def
                 tcb_release_enqueue_upd_def insort_filter_def)

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
  apply (wpsimp wp: valid_sched_wp)
  by (auto elim!: valid_blockedE' simp: in_queue_2_def tcb_release_enqueue_upd_def insort_filter_def)

lemma set_map_fst_filter_zip:
  "set (map fst (filter P (zip xs ys))) \<subseteq> set xs"
  apply (induct xs, simp)
  apply (case_tac ys; simp)
  by (metis (mono_tags, lifting) image_Collect_subsetI insertI2 set_zip_helper)

lemma tcb_release_enqueue_not_in_release_q_other[wp]:
  "\<lbrace>K (t \<noteq> t') and not_in_release_q t'\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>_. not_in_release_q t'\<rbrace>"
  unfolding tcb_release_enqueue_def
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: mapM_wp_inv)
  apply wpsimp
  apply (simp add: not_in_release_q_def in_release_q_def in_queue_2_def)
  using set_map_fst_filter_zip by fastforce

lemma tcb_release_enqueue_ready_or_release[wp]:
  "\<lbrace>ready_or_release and not_queued t\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  unfolding ready_or_release_2_def pred_conj_def
  apply (rule_tac Q="\<lambda>x. (\<forall>t'. \<not> (in_ready_q t' x \<and> in_release_q t' x) \<and> not_queued t x)"
               in hoare_weaken_pre[rotated], simp)
  apply (rule hoare_vcg_all_lift)
  apply (simp only: de_Morgan_conj)
  apply (case_tac "t = t'")
   apply (rule hoare_weaken_pre)
    apply (rule hoare_post_disjI1[simplified pred_disj_def])
    apply wpsimp
   apply blast
  apply (rule_tac Q="\<lambda>s. not_queued t' s \<or> not_in_release_q t' s" in hoare_weaken_pre)
   apply (rule hoare_vcg_disj_lift)
    apply wpsimp+
  done

lemma tcb_release_enqueue_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
        \<and> not_queued thread s
        \<and> not_in_release_q thread s
        \<and> scheduler_act_not thread s
        \<and> pred_map runnable (tcb_sts_of s) thread
        \<and> active_sc_tcb_at thread s\<rbrace>
   tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  by (wpsimp simp: valid_sched_def)

lemma tcb_release_enqueue_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
        \<and> valid_blocked_except thread s
        \<and> not_queued thread s
        \<and> not_in_release_q thread s
        \<and> scheduler_act_not thread s
        \<and> pred_map runnable (tcb_sts_of s) thread
        \<and> active_sc_tcb_at thread s\<rbrace>
   tcb_release_enqueue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: tcb_release_enqueue_valid_blocked_except_set simp: valid_sched_def)

lemma valid_blocked_thread_lift_except:
  "valid_blocked_thread nq nr S qs rq sa ct sts scps cfgs t
   \<longleftrightarrow> (t \<notin> S \<longrightarrow> valid_blocked_thread nq nr {} qs rq sa ct sts scps cfgs t)"
  by (auto simp: valid_blocked_thread_def)

lemma valid_blocked_divided_except_set:
  "valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
   \<longleftrightarrow> valid_blocked_except_set_2 (S \<union> except) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
       \<and> valid_blocked_except_set_2 (- S \<union> except) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  by (auto simp add: valid_blocked_defs)

lemma valid_blocked_divided_threadsE:
  assumes "valid_blocked_except_set_2 (I \<union> S) queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes " \<forall>t \<in> I. valid_blocked_thread id id {} queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  shows "valid_blocked_except_set_2 S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  apply (rule valid_blocked_divided_except_set[THEN iffD2], rule conjI, rule assms)
  by (clarsimp simp: valid_blocked_except_set_2_def[where except="-I \<union> S"]
                     valid_blocked_thread_lift_except[where S="-I \<union> S"]
                     assms)

lemmas valid_blocked_divided_threadE
  = valid_blocked_divided_threadsE[where I="{t}", simplified] for t

lemma test_possible_switch_to_valid_sched:
  "\<lbrace>\<lambda>s. if pred_map runnable (tcb_sts_of s) target \<and> active_sc_tcb_at target s \<and> not_in_release_q target s
        then valid_sched_except_blocked s \<and> valid_blocked_except target s
              \<and> target \<noteq> idle_thread s \<and> budget_ready target s \<and> budget_sufficient target s
        else valid_sched s\<rbrace>
   test_possible_switch_to target
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_sched_strong is_schedulable_wp'
              simp: test_possible_switch_to_def)
  by (auto simp: vs_all_heap_simps)

(* sc_ptr is linked to a thread that is not in any queue *)
lemma postpone_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
        \<and> (\<forall>tp. pred_map_eq (Some tp) (sc_tcbs_of s) sc_ptr
                \<longrightarrow> valid_blocked_except tp s \<and> pred_map runnable (tcb_sts_of s) tp
                    \<and> scheduler_act_not tp s \<and> not_in_release_q tp s
                    \<and> active_sc_tcb_at tp s)\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: tcb_release_enqueue_valid_sched
                    tcb_dequeue_not_queued
                    tcb_sched_dequeue_valid_sched_except_blocked
                    tcb_sched_dequeue_valid_blocked_except_set
                    get_sc_obj_ref_wp)
  by (clarsimp simp: valid_sched_def sc_tcb_sc_at_def obj_at_def vs_all_heap_simps)

lemma postpone_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
        \<and> (\<forall>tp. pred_map_eq (Some tp) (sc_tcbs_of s) sc_ptr
                \<longrightarrow> pred_map runnable (tcb_sts_of s) tp \<and> scheduler_act_not tp s
                    \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s)\<rbrace>
    postpone sc_ptr
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched_except_blocked
            tcb_sched_dequeue_valid_blocked_except_set
            tcb_dequeue_not_queued
            tcb_sched_dequeue_valid_ready_qs
            tcb_sched_dequeue_valid_sched_except_blocked)
  by (clarsimp simp: valid_sched_def obj_at_kh_kheap_simps pred_map_eq_normalise)

lemma postpone_valid_ready_qs:
  "\<lbrace>valid_ready_qs \<rbrace>
     postpone sc_ptr
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: tcb_sched_dequeue_valid_ready_qs get_sc_obj_ref_wp)

lemma postpone_valid_release_q:
  "\<lbrace> valid_release_q and
     (\<lambda>s. \<forall> tp. sc_tcb_sc_at ((=) (Some tp)) sc_ptr s \<longrightarrow>
     pred_map runnable (tcb_sts_of s) tp
      \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s)\<rbrace>
     postpone sc_ptr
   \<lbrace> \<lambda>_. valid_release_q \<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: tcb_release_enqueue_valid_release_q get_sc_obj_ref_wp)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def )

crunches sched_context_resume
  for valid_ready_qs[wp]: valid_ready_qs
  and released_ipc_queues[wp]: released_ipc_queues
  (wp: crunch_wps)

lemma sched_context_resume_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace>
   sched_context_resume sc_ptr_opt
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_release_q is_schedulable_wp
              simp: thread_get_def)
  by (clarsimp simp: sc_tcb_sc_at_def is_schedulable_bool_def obj_at_def
                     is_sc_active_kh_simp vs_all_heap_simps
              dest!: get_tcb_SomeD split: option.splits)

lemma tcb_release_enqueue_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
   tcb_release_enqueue tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. weak_valid_sched_action_2 {} (cur_time s) (scheduler_action s) (tcb_ptr # qs) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: )
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
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace> "
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_sched_action thread_get_wp is_schedulable_wp)
  by (fastforce simp: obj_at_def is_schedulable_bool_def is_tcb
               dest!: get_tcb_SomeD split: option.splits)

lemma sched_context_resume_valid_sched_action_with_sym_refs:
  "\<lbrace>valid_sched_action and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_sched_action thread_get_wp is_schedulable_wp
              simp: get_tcb_queue_def)
  apply (clarsimp simp: obj_at_def scheduler_act_not_def valid_sched_action_def
                        weak_valid_sched_action_def sc_at_pred_n_def vs_all_heap_simps)
  apply (frule sym_ref_sc_tcb; simp?)
  by force

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
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace> "
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_sched_action_with_invs thread_get_wp is_schedulable_wp)
  apply (fastforce simp: obj_at_def is_schedulable_bool_def is_tcb
                  dest!: get_tcb_SomeD split: option.splits)
  done

lemma weak_valid_sched_action_contrap:
  "weak_valid_sched_action s \<Longrightarrow> (simple_sched_action s \<or>
     \<not> pred_map runnable (tcb_sts_of s) ref \<or> \<not> released_sc_tcb_at ref s \<or>
     in_release_queue ref s) \<Longrightarrow> scheduler_act_not ref s"
  by (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def simple_sched_action_def in_release_queue_def)

lemma valid_ready_qs_contrap:
  "valid_ready_qs s
   \<Longrightarrow> (\<not> pred_map runnable (tcb_sts_of s) ref \<or> \<not> released_sc_tcb_at ref s) \<Longrightarrow> not_queued ref s"
  by (clarsimp simp: valid_ready_qs_def in_ready_q_def)

lemma sched_context_resume_valid_sched_except_blocked:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> heap_refs_retract_at (sc_tcbs_of s) (tcb_scps_of s) scp\<rbrace>
   sched_context_resume scp
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (wpsimp wp: postpone_valid_sched_except_blocked is_schedulable_wp' get_tcb_queue_wp thread_get_wp'
              simp: sched_context_resume_def refill_sufficient_def get_refills_def refill_ready_def)
  apply (clarsimp simp: valid_sched_def sc_at_pred_n_def get_tcb_ko_at obj_at_def)
  apply (frule (1) heap_refs_retract_atD, clarsimp simp: vs_all_heap_simps)
  apply (prop_tac "\<not> released_sc_tcb_at tp s", clarsimp simp: vs_all_heap_simps refill_ready_def refill_sufficient_def)
  by (auto elim!: weak_valid_sched_action_contrap[OF valid_sched_action_weak_valid_sched_action])

(* FIXME RT: duplicates proof in sched_context_resume_valid_sched_except_blocked,
             because we're missing proofs about sched_context_resume and valid_blocked. *)
lemma sched_context_resume_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> heap_refs_retract_at (sc_tcbs_of s) (tcb_scps_of s) scp\<rbrace>
   sched_context_resume scp
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: postpone_valid_sched is_schedulable_wp' get_tcb_queue_wp thread_get_wp'
              simp: sched_context_resume_def refill_sufficient_def get_refills_def refill_ready_def)
  apply (clarsimp simp: valid_sched_def sc_at_pred_n_def get_tcb_ko_at obj_at_def)
  apply (frule (1) heap_refs_retract_atD, clarsimp simp: vs_all_heap_simps)
  apply (prop_tac "\<not> released_sc_tcb_at tp s", clarsimp simp: vs_all_heap_simps refill_ready_def refill_sufficient_def)
  by (auto elim!: weak_valid_sched_action_contrap[OF valid_sched_action_weak_valid_sched_action])

lemma postpone_valid_blocked_except_set:
  "postpone sc_ptr \<lbrace>valid_blocked_except_set S\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac tcb_opt; clarsimp)
  apply (rename_tac tptr)
  by (wpsimp wp: tcb_release_enqueue_valid_blocked_except_set tcb_sched_dequeue_valid_blocked_except_set)

crunches sched_context_resume
  for not_cur_thread[wp]: "not_cur_thread t"
  and bound_sc_obj_tcb_at[wp]: "\<lambda>s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s)"
  and valid_blocked_except_set[wp]: "valid_blocked_except_set S"
  and not_cur_thread'[wp]: "\<lambda>s. P (not_cur_thread t s)"
    (wp: crunch_wps)

lemmas sched_context_resume_valid_blocked = sched_context_resume_valid_blocked_except_set
             [of "{}", simplified]

crunch simple[wp]: suspend,sched_context_unbind_ntfn simple_sched_action
  (wp: maybeM_wp hoare_drop_imps)

lemma in_set_tcb_sched_dequeue:
  "t \<in> set (tcb_sched_dequeue k (ready_queues s a b)) \<Longrightarrow>
   t \<in> set (ready_queues s a b) \<and> t \<noteq> k"
 by (auto simp: tcb_sched_dequeue_def)

lemma set_thread_state_not_active_helper:
  "\<lbrace>\<lambda>s. \<not> active k\<rbrace> set_thread_state t k \<lbrace>\<lambda>rv s. (st_tcb_at active t s \<longrightarrow> \<not> active_sc_tcb_at t s)\<rbrace>"
  apply (rule hoare_strengthen_post[where Q="\<lambda>rv s. (\<not>st_tcb_at active t s)"])
  apply (wpsimp simp: set_thread_state_def wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)+
  done

(* FIXME maybe move? *)
lemma weak_valid_sched_action_st_prop:
  "\<lbrakk>weak_valid_sched_action s; scheduler_action s = switch_thread t\<rbrakk> \<Longrightarrow>
       pred_map runnable (tcb_sts_of s) t \<and> released_sc_tcb_at t s"
  by (clarsimp simp: weak_valid_sched_action_def)

crunch not_in_release_q[wp]: cancel_ipc "not_in_release_q t"
  (simp: crunch_simps  wp: crunch_wps tcb_release_remove_not_in_release_q')

crunches cancel_ipc
  for ready_or_release[wp]: "ready_or_release"
  (wp: hoare_drop_imps)

lemma suspend_ready_or_release[wp]:
  "suspend t \<lbrace>ready_or_release\<rbrace>"
  unfolding suspend_def
  by (wpsimp wp: hoare_drop_imps simp: update_restart_pc_def)

lemma suspend_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not t\<rbrace>
   suspend t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding suspend_def update_restart_pc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (wpsimp wp: valid_sched_wp simp: valid_sched_def)
  apply (intro conjI)
         apply (clarsimp simp: tcb_sched_dequeue_def valid_ready_queued_thread_2_def vs_all_heap_simps
                        split: if_splits elim!: valid_ready_qsE)
        apply (clarsimp simp: valid_release_q_def tcb_sched_dequeue_def tcb_sts.pred_map_upds
                              sorted_release_q_2_def)
       apply (clarsimp simp: tcb_sched_dequeue_def ready_or_release_2_def in_queues_2_def
                             in_queue_2_def)
       apply (rename_tac t' d p)
       apply (prop_tac "t' \<in> set ((ready_queues s) d p)")
        apply (case_tac "dom = d \<and> prio = p"; clarsimp?)
        apply presburger
       apply blast
      apply (clarsimp simp: ct_not_in_q_def tcb_sched_dequeue_def in_queues_2_def split: if_splits)
     apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def tcb_sched_dequeue_def
                           scheduler_act_not_def is_activatable_def tcb_sts.pred_map_upds
                    split: if_splits)
    apply (clarsimp simp: ct_in_cur_domain_def)
   apply (clarsimp simp: tcb_sts.pred_map_upds if_bool_simps
                         tcb_sched_ready_q_update_in_queues_2_simps in_ready_q_def
                         tcb_sched_act_in_queues_2_simps in_release_q_def
                  elim!: valid_blockedE')
  by (simp add: released_ipc_queues_except_strengthen[unfolded fun_upd_def])

lemma tcb_sched_context_update_None_valid_sched:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except ref and not_queued ref and not_in_release_q ref and scheduler_act_not ref\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update ref None
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                 set_tcb_sched_context_valid_release_q_not_queued
                 set_tcb_sched_context_None_valid_blocked
                 set_tcb_sched_context_None_released_ipc_queues
                 set_tcb_sched_context_valid_sched_action_act_not)

lemma sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and
   (\<lambda>s. \<forall>thread. sc_tcb_sc_at ((=) (Some thread)) sc_ptr s \<longrightarrow> (scheduler_act_not thread s))\<rbrace>
   sched_context_unbind_tcb sc_ptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  unfolding sched_context_unbind_tcb_def
  apply (wpsimp wp: tcb_sched_context_update_None_valid_sched tcb_release_remove_valid_blocked_except
                    tcb_sched_dequeue_valid_ready_qs tcb_sched_dequeue_valid_blocked_except_set tcb_dequeue_not_queued
                    reschedule_required_valid_blocked
              simp: valid_sched_def)
  by (clarsimp simp: sc_at_pred_n_def obj_at_def)

(* This precondition is nasty, but it's better than passing through sym_refs *)
lemma maybe_sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and
   (\<lambda>s. \<forall>scp tp. bound_sc_tcb_at (\<lambda>x. x = Some scp) tcb_ptr s \<longrightarrow>
                 sc_tcb_sc_at (\<lambda>x. x = Some tp) scp s \<longrightarrow>
                 scheduler_act_not tp s)\<rbrace>
   maybe_sched_context_unbind_tcb tcb_ptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  unfolding maybe_sched_context_unbind_tcb_def
  apply (wpsimp wp: sched_context_unbind_tcb_valid_sched get_tcb_obj_ref_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def sc_at_pred_n_def)

lemma sched_context_unbind_all_tcbs_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
   sched_context_unbind_all_tcbs sc_ptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  unfolding sched_context_unbind_all_tcbs_def
  by (wpsimp wp: sched_context_unbind_tcb_valid_sched)

lemma sched_context_unbind_reply_valid_sched_misc[wp]:
  "sched_context_unbind_reply sc_ptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (tcbs_of s) (sc_refill_cfgs_of s)\<rbrace>"
  unfolding sched_context_unbind_reply_def
  by (wpsimp wp: get_sched_context_wp update_sched_context_wp update_sk_obj_ref_wp
           simp: obj_at_def vs_all_heap_simps fun_upd_def tcb_heap.all_simps)

lemma sched_context_unbind_reply_non_empty_sc_replies_at[wp]:
  "\<lbrace>\<lambda>s. scp' \<noteq> scp \<longrightarrow> \<not> non_empty_sc_replies_at scp' s\<rbrace>
   sched_context_unbind_reply scp
   \<lbrace>\<lambda>rv s. \<not> non_empty_sc_replies_at scp' s\<rbrace>"
  unfolding sched_context_unbind_reply_def
  by (wpsimp wp: update_sc_replies_valid_sched_pred simp: heap_upd_def vs_all_heap_simps obj_at_kh_kheap_simps)

lemma active_reply_sc_at_lift_pre_conj:
  assumes "\<lbrace>\<lambda>s. \<not> non_empty_sc_replies_at scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> non_empty_sc_replies_at scp s\<rbrace>"
  assumes "\<lbrace>\<lambda>s. pred_map active_scrc (sc_refill_cfgs_of s) scp \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  shows "\<lbrace>\<lambda>s. active_if_reply_sc_at scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_if_reply_sc_at scp s\<rbrace>"
  unfolding active_if_reply_sc_at_2_def by (intro hoare_vcg_imp_lift_N_pre_conj assms)

lemma sched_context_unbind_reply_active_reply_scs[wp]:
  "sched_context_unbind_reply sc_ptr \<lbrace>active_reply_scs\<rbrace>"
  by (wpsimp wp: active_reply_scs_lift_pre_conj active_reply_sc_at_lift_pre_conj)

lemma sched_context_unbind_reply_valid_sched[wp]:
  "sched_context_unbind_reply scp \<lbrace>valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def)

lemma fast_finalise_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action and (\<lambda>s. \<exists>slot. cte_wp_at ((=) cap) slot s)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (cases cap; clarsimp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_valid_sched, intro conjI; clarsimp)
    apply wpsimp
      apply (strengthen invs_valid_idle invs_sym_refs, simp)
      apply (wpsimp wp: unbind_maybe_notification_invs)
     apply (wpsimp, clarsimp)
   apply (wpsimp wp: cancel_ipc_valid_sched get_simple_ko_wp
                     reply_remove_valid_sched gts_wp)
   apply (simp add: pred_tcb_at_eq_commute tcb_at_kh_simps pred_map_def)
  apply (wpsimp wp: set_sc_refill_max_valid_sched_unbound_sc hoare_vcg_all_lift
                          sched_context_unbind_all_tcbs_valid_sched)
  apply (rename_tac sc n tp)
   apply (rule_tac Q="\<lambda>ya. invs and sc_tcb_sc_at (\<lambda>x. x = None) sc"
                          in hoare_strengthen_post[rotated])
    apply (clarsimp simp: tcb_at_kh_simps[symmetric] pred_tcb_at_eq_commute)
    apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
   apply (wpsimp wp: sched_context_unbind_yield_from_invs)
  apply (clarsimp split: if_splits)
  apply (fastforce simp: invs_def valid_state_def cap_range_def dest!: valid_global_refsD)
  done

context DetSchedSchedule_AI begin

lemma cap_delete_one_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action\<rbrace>
   cap_delete_one slot
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (cases slot; wpsimp wp: fast_finalise_valid_sched get_cap_wp; fastforce)

lemma deleting_irq_handler_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action\<rbrace>
   deleting_irq_handler irq
   \<lbrace>\<lambda>y. valid_sched:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by (wpsimp wp: cap_delete_one_valid_sched)

lemma unbind_from_sc_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
   unbind_from_sc tcb_ptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  unfolding unbind_from_sc_def
  by (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift maybeM_wp sched_context_unbind_tcb_valid_sched)

(* precondition could be weaker (invs > (sym_refs and valid_objs and (\<lambda>s. cap \<noteq> ThreadCap idle_thread_ptr)) but
   this is much simpler to prove *)
lemma finalise_cap_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and simple_sched_action and (\<lambda>s. \<exists>slot. cte_wp_at ((=) cap) slot s)\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (case_tac cap; (solves \<open>wpsimp\<close>)?; simp)
       apply (wpsimp wp: cancel_all_ipc_valid_sched cancel_ipc_valid_sched get_simple_ko_wp
                   simp: invs_valid_objs
                  split: if_splits, fastforce)
      apply ((wpsimp wp: cancel_ipc_valid_sched gts_wp get_simple_ko_wp
                         unbind_maybe_notification_invs
                 split: if_splits | strengthen invs_valid_idle invs_sym_refs)+)[1]
     apply ((wpsimp wp: cancel_ipc_valid_sched reply_remove_valid_sched gts_wp get_simple_ko_wp
                split: if_splits| strengthen invs_valid_idle invs_sym_refs)+)[1]
     apply (simp add: pred_tcb_at_eq_commute)
     apply (clarsimp simp: tcb_at_kh_simps pred_map_def)
    apply (wpsimp wp: suspend_valid_sched)
      apply (rule_tac Q="\<lambda>ya. valid_sched and invs and scheduler_act_not x7 and tcb_at x7"
                      in hoare_strengthen_post)
       apply (wpsimp wp: unbind_from_sc_valid_sched)
      apply fastforce
     apply (wpsimp wp: unbind_notification_invs split: if_splits)
    apply (subgoal_tac "valid_cap cap s")
     apply (clarsimp simp: valid_cap_def split: if_splits)
     apply (frule(1) valid_global_refsD[OF invs_valid_global_refs _ idle_global])
     apply (clarsimp dest!: invs_valid_idle simp: valid_idle_def cap_range_def)
    apply (clarsimp elim!: cte_wp_valid_cap)
   apply (rename_tac scptr x)
   apply (wpsimp wp: set_sc_refill_max_valid_sched_unbound_sc hoare_vcg_all_lift)
    apply (rule_tac Q="\<lambda>ya. invs and sc_tcb_sc_at (\<lambda>x. x = None) scptr"
                 in hoare_strengthen_post[rotated])
     apply (clarsimp simp: tcb_at_kh_simps(3)[symmetric] pred_tcb_at_eq_commute)
     apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl])
      apply clarsimp
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
    apply (wpsimp wp: sched_context_unbind_yield_from_invs)
   apply (clarsimp split: if_splits)
   apply (fastforce simp: invs_def valid_state_def cap_range_def dest!: valid_global_refsD)
  apply (wpsimp wp: deleting_irq_handler_valid_sched)
  done

lemma cancel_all_ipc_simple_sched_action[wp]:
  "cancel_all_ipc ep \<lbrace>simple_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: cancel_all_ipc_def)

lemma cancel_all_ipc_scheduler_act_sane[wp]:
  "cancel_all_ipc ep \<lbrace>scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: cancel_all_ipc_def)

lemma cancel_all_signals_simple_sched_action[wp]:
  "cancel_all_signals ntfn \<lbrace>simple_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: cancel_all_signals_def)

lemma cancel_all_signals_scheduler_act_sane[wp]:
  "cancel_all_signals ntfn \<lbrace>scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: cancel_all_signals_def)

crunches fast_finalise, cap_delete_one, deleting_irq_handler, cancel_ipc, suspend,
         sched_context_unbind_all_tcbs, finalise_cap
  for simple[wp]: "simple_sched_action :: 'state_ext state \<Rightarrow> _"
  and scheduler_act_sane[wp]: "scheduler_act_sane :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps )

end

lemma update_time_stamp_valid_sched_misc[wp]:
  "update_time_stamp \<lbrace>\<lambda>s. P (cur_sc s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s) (ep_send_qs_of s) (ep_recv_qs_of s)\<rbrace>"
  unfolding update_time_stamp_def
  by wpsimp

context DetSchedSchedule_AI_det_ext begin

lemma rec_del_valid_sched:
 "\<lbrace>valid_sched and simple_sched_action and invs and valid_rec_del_call args
        and (\<lambda>s. \<not> exposed_rdcall args
               \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
        and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                       \<not> cap_removeable cap sl
                       \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                  | _ \<Rightarrow> True)\<rbrace>
  rec_del args
  \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_post_impErr)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs''[where Q="valid_sched and simple_sched_action"])
         apply wpsimp+
      apply (wpsimp wp: preemption_point_inv')+
  done

lemma rec_del_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
   by (wpsimp wp: rec_del_preservation preemption_point_inv')

end

lemma possible_switch_to_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane and (\<lambda>s. scheduler_action s = resume_cur_thread \<longrightarrow> not_in_release_q t s \<longrightarrow> t \<noteq> cur_thread s)\<rbrace>
   possible_switch_to t
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: set_scheduler_action_wp get_tcb_obj_ref_wp thread_get_wp)
  by (clarsimp simp: scheduler_act_sane_def obj_at_def is_tcb)

(* FIXME: add this to elim set much higher up *)
declare pred_tcb_at_tcb_at[elim!]

lemma possible_switch_to_scheduler_act_sane':
  "\<lbrace>scheduler_act_sane and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   possible_switch_to t
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: set_scheduler_action_wp get_tcb_obj_ref_wp thread_get_wp)
  by (clarsimp simp: scheduler_act_sane_def obj_at_def is_tcb)

lemma restart_thread_if_no_fault_scheduler_act_sane[wp]:
 "\<lbrace>scheduler_act_sane and (\<lambda>s. xa \<noteq> cur_thread s) \<rbrace>
  restart_thread_if_no_fault xa
  \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: set_thread_state_def set_thread_state_act_def thread_get_def
               wp: possible_switch_to_scheduler_act_sane set_scheduler_action_wp is_schedulable_wp
                   set_object_wp
                   hoare_vcg_imp_lift' )

lemma tcb_sched_enqueue_ct_not_queued:
  "\<lbrace> ct_not_queued and (\<lambda>s. cur \<noteq> cur_thread s)\<rbrace>
   tcb_sched_action tcb_sched_enqueue cur
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: set_tcb_queue_wp)
  by (clarsimp simp: in_queues_2_def tcb_sched_ready_q_update_set_simps)

lemma possible_switch_to_ct_not_queued:
  "\<lbrace>ct_not_queued and (\<lambda>s. t \<noteq> cur_thread s) and scheduler_act_sane\<rbrace> possible_switch_to t \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: tcb_sched_enqueue_ct_not_queued thread_get_wp)
  done

lemma restart_thread_if_no_fault_ct_not_queued[wp]:
 "\<lbrace>ct_not_queued and scheduler_act_sane and (\<lambda>s. xa \<noteq> cur_thread s)\<rbrace>
  restart_thread_if_no_fault xa
  \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: set_thread_state_def set_thread_state_act_def thread_get_def
               wp: possible_switch_to_ct_not_queued set_scheduler_action_wp is_schedulable_wp
                   set_object_wp
                   hoare_vcg_imp_lift' )

crunches cancel_all_ipc
  for ct_not_in_release_q[wp]: "ct_not_in_release_q"
  (wp: crunch_wps)

crunches update_time_stamp
  for typ_at[wp]: "\<lambda>s. P (typ_at T t  s)"

crunches update_time_stamp
  for obj_at[wp]: "\<lambda>(s). Q (obj_at P t s)"

context DetSchedSchedule_AI begin

lemma dmo_getCurrentTime_sp[wp]:
  "do_machine_op getCurrentTime \<lbrace>P\<rbrace> \<Longrightarrow>
   \<lbrace>valid_machine_time and P :: 'state_ext state \<Rightarrow> _\<rbrace>
   do_machine_op getCurrentTime
   \<lbrace>\<lambda>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1) \<and> P s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. P s \<and> ((cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1))" in hoare_strengthen_post)
  apply (wp hoare_vcg_conj_lift)
  apply (rule dmo_getCurrentTime_vmt_sp)
  by simp+

(* This is not strictly a weakest precondition rule, but it is quite close. *)
lemma dmo_getCurrentTime_wp:
  assumes str_post: "\<And>rv s. (cur_time s \<le> rv) \<and> (rv \<le> - kernelWCET_ticks - 1) \<and> P s \<longrightarrow> Q rv s"
  assumes dmo_inv: "do_machine_op getCurrentTime \<lbrace>P\<rbrace>"
  shows "\<lbrace>valid_machine_time and P :: 'state_ext state \<Rightarrow> _\<rbrace>
         do_machine_op getCurrentTime
         \<lbrace>\<lambda>rv s. Q rv s\<rbrace>"
  apply (strengthen str_post)
  by (wpsimp wp: dmo_getCurrentTime_vmt_sp dmo_inv)

lemma update_time_stamp_is_refill_ready[wp]:
  "\<lbrace>valid_machine_time and is_refill_ready scp :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_. is_refill_ready scp\<rbrace>"
  unfolding update_time_stamp_def
  apply (wpsimp wp: dmo_getCurrentTime_wp)
     prefer 2
     apply (rule_tac Q="(is_refill_ready scp and (\<lambda>s. cur_time s = prev_time))"
            in hoare_weaken_pre[rotated], assumption)
     apply wpsimp
    apply (clarsimp simp: vs_all_heap_simps refill_ready_def)
    apply (rule_tac b="cur_time s + kernelWCET_ticks" in order.trans, simp)
    apply (rule word_plus_mono_left, simp)
    apply (subst olen_add_eqv)
    apply (subst add.commute)
    apply (rule no_plus_overflow_neg)
    apply (erule word_leq_minus_one_le[rotated])
  using kernelWCET_ticks_non_zero
    apply fastforce
   apply wpsimp
  by simp

lemma update_time_stamp_budget_ready[wp]:
 "\<lbrace>budget_ready t and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_. budget_ready t\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>scp. bound_sc_tcb_at (\<lambda>ko. ko = Some scp) t s \<and>
                                 is_refill_ready scp s"
   in hoare_strengthen_post)
   apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_imp_lift)
   apply (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)
  apply (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)
  done

lemma tcb_sched_dequeue_ct_not_queued:
  "tcb_sched_action tcb_sched_dequeue x \<lbrace>ct_not_queued\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp tcb_dequeue_not_queued_gen, simp)

lemma sym_refs_SendEP_ipc_queued_thread:
  "\<lbrakk> kheap s ptr = Some (Endpoint (SendEP q)); sym_refs (state_refs_of s); t \<in> set q \<rbrakk>
   \<Longrightarrow> ipc_queued_thread t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ptr in allE)
  apply (drule_tac x = "(t, EPSend)" in bspec)
   apply (clarsimp simp: state_refs_of_def)
  apply (clarsimp simp: state_refs_of_def refs_of_def split: option.splits)
  apply (case_tac x2;
         clarsimp simp: get_refs_def tcb_st_refs_of_def vs_all_heap_simps
                 split: option.splits thread_state.splits)
  done

lemma sym_refs_RecvEP_ipc_queued_thread:
  "\<lbrakk> kheap s ptr = Some (Endpoint (RecvEP q)); sym_refs (state_refs_of s); t \<in> set q \<rbrakk>
   \<Longrightarrow> ipc_queued_thread t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ptr in allE)
  apply (drule_tac x = "(t, EPRecv)" in bspec)
   apply (clarsimp simp: state_refs_of_def)
  apply (clarsimp simp: state_refs_of_def refs_of_def split: option.splits)
  apply (case_tac x2;
         clarsimp simp: get_refs_def tcb_st_refs_of_def vs_all_heap_simps
                 split: option.splits thread_state.splits)
  done

lemma sym_refs_WaitingNtfn_ipc_queued_thread:
  "\<lbrakk> kheap s ptr = Some (Notification (ntfn)); ntfn_obj ntfn = WaitingNtfn q;  sym_refs (state_refs_of s); t \<in> set q \<rbrakk>
   \<Longrightarrow> ipc_queued_thread t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ptr in allE)
  apply (drule_tac x = "(t, NTFNSignal)" in bspec)
   apply (clarsimp simp: state_refs_of_def ntfn_q_refs_of_def)
  apply (clarsimp simp: state_refs_of_def refs_of_def split: option.splits)
  apply (case_tac x2;
         clarsimp simp: get_refs_def tcb_st_refs_of_def vs_all_heap_simps
                 split: option.splits thread_state.splits)
  done

lemma cancel_all_ipc_ct_not_queued:
  "\<lbrace>ct_not_queued and scheduler_act_sane and invs and ct_not_blocked\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>_. ct_not_queued:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cancel_all_ipc_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ep=IdleEP"; simp?)
   apply wpsimp
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and ct_not_queued and scheduler_act_sane and invs and ct_not_blocked) s" in hoare_weaken_pre)
     apply (rule hoare_seq_ext[OF _ get_epq_sp])
     apply wpsimp
       apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> t \<noteq> cur_thread x)" in hoare_strengthen_post)
        apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
         prefer 2
         apply (rule subset_refl, clarsimp, clarsimp)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (clarsimp simp: obj_at_def)
     apply (subgoal_tac "ipc_queued_thread (cur_thread s) s")
      apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps pred_map_simps)
     apply (erule sym_refs_SendEP_ipc_queued_thread; clarsimp)
    apply assumption
   apply (rule_tac Q="\<lambda>s. (ko_at (Endpoint ep) epptr and ct_not_queued and scheduler_act_sane and invs and ct_not_blocked) s" in hoare_weaken_pre)
    apply (rule hoare_seq_ext[OF _ get_epq_sp])
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>x. \<forall>t. t \<in> set (queue) \<longrightarrow> t \<noteq> cur_thread x)" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp hoare_vcg_all_lift hoare_vcg_imp_lift' gts_wp)
        prefer 2
        apply (rule subset_refl, clarsimp, clarsimp)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (clarsimp simp: obj_at_def)
    apply (subgoal_tac "ipc_queued_thread (cur_thread s) s")
     apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps pred_map_simps)
    apply (erule sym_refs_RecvEP_ipc_queued_thread; clarsimp)
   apply assumption
  apply fastforce
  done

lemma cancel_all_signals_ct_not_queued:
 "\<lbrace>ct_not_queued and scheduler_act_sane and invs and ct_not_blocked:: 'state_ext state \<Rightarrow> _\<rbrace>
  cancel_all_signals f
  \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  unfolding cancel_all_signals_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply wpc
     apply wpsimp
    apply (rule_tac Q="\<lambda>s. (ko_at (Notification ntfn) f and ct_not_queued and scheduler_act_sane and invs and ct_not_blocked) s" in hoare_weaken_pre[rotated])
     apply assumption
    apply wpsimp
      apply (rule_tac Q="\<lambda>_. ct_not_queued and scheduler_act_sane and (\<lambda>s. \<forall>x \<in> set x2. x \<noteq> (cur_thread s))" in hoare_strengthen_post)
       apply (wpsimp wp: mapM_x_wp[where xs = t and S = "set t" for t, simplified])
        apply (wpsimp wp: possible_switch_to_scheduler_act_sane' possible_switch_to_ct_not_queued)+
       apply fastforce
      apply fastforce
     apply (wpsimp wp: )+
    apply (clarsimp simp: obj_at_def)
    apply (subgoal_tac "ipc_queued_thread (cur_thread s) s")
     apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps pred_map_simps)
    apply (erule (1) sym_refs_WaitingNtfn_ipc_queued_thread; clarsimp)
   apply wpsimp
  apply clarsimp
  done

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn, cancel_ipc
  for ct_not_queued[wp]: "ct_not_queued :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

crunches reply_remove, suspend, complete_yield_to, sched_context_unbind_tcb, unbind_notification,
         sched_context_unbind_yield_from, sched_context_unbind_reply, sched_context_unbind_ntfn,
         sched_context_unbind_all_tcbs
  for ct_not_queued[wp]: "ct_not_queued :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp tcb_sched_dequeue_ct_not_queued simp: crunch_simps ignore: tcb_sched_action)

crunches deleting_irq_handler
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

lemma unbind_from_sc_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace>
   unbind_from_sc x7
   \<lbrace>\<lambda>_. ct_not_queued:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding unbind_from_sc_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)

lemma set_tcb_obj_ref_cur_sc_chargeable_const:
  "(\<And>t. tcb_sched_context (f (\<lambda>y. val) t) = tcb_sched_context t \<and>
         tcb_state (f (\<lambda>y. val) t) = tcb_state t) \<Longrightarrow>
   set_tcb_obj_ref f tptr val \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: cur_sc_chargeable_def vs_all_heap_simps obj_at_kh_kheap_simps)

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

lemmas misc_cur_sc_chargeable_const =  set_tcb_obj_ref_cur_sc_chargeable_const
                                       thread_set_cur_sc_chargeable_const

lemma sched_context_unbind_tcb_cur_sc_chargeable[wp]:
  "sched_context_unbind_tcb xb \<lbrace>cur_sc_chargeable\<rbrace>"
  unfolding sched_context_unbind_tcb_def
  apply (wp)
  apply (simp add: cur_sc_chargeable_def2)
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (rule_tac Q="\<lambda>_. cur_sc_chargeable" in hoare_strengthen_post[rotated])
  apply (clarsimp simp: cur_sc_chargeable_def2 obj_at_def pred_tcb_at_def sc_at_pred_def, fastforce)
  apply wpsimp+
  done

crunches sched_context_unbind_yield_from, sched_context_unbind_all_tcbs, unbind_from_sc
  for cur_sc_chargeable[wp]: cur_sc_chargeable
  (wp: misc_cur_sc_chargeable_const crunch_wps maybeM_inv)

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
           apply (wpsimp wp: update_sched_context_wp)
          apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
                 in hoare_strengthen_post[rotated])
           apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def pred_map_simps split: if_split, fastforce)
          apply (wpsimp simp: test_reschedule_def)
             apply (wpsimp wp: set_tcb_obj_ref_wp)
            apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
                   in hoare_strengthen_post[rotated])
             apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def pred_map_simps cur_tcb_def is_tcb split: if_split, fastforce)
            apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)
           apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp assert_opt_inv)
          apply (wpsimp wp: assert_opt_inv)
         apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)
        apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and cur_tcb and (\<lambda>s. t \<noteq> cur_thread s)"
               in hoare_strengthen_post[rotated])
         apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def pred_map_simps split: if_split)
        apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def pred_map_simps split: if_split)
  done

lemma set_thread_state_csctb:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. (\<forall>x. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<longrightarrow> (x \<noteq> xa \<or> d = Inactive)))\<rbrace>
   set_thread_state xa d
   \<lbrace>\<lambda>xa. cur_sc_chargeable\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)

lemma set_thread_state_Inactive_csctb[wp]:
  "set_thread_state d Inactive \<lbrace>cur_sc_chargeable\<rbrace>"
  by (wpsimp wp: set_thread_state_csctb)

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
  by (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)

lemma restart_thread_if_no_fault_not_bound_sc_tcb_at[wp]:
  "restart_thread_if_no_fault x \<lbrace>\<lambda>s. \<not> bound_sc_tcb_at P xs s\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by wpsimp

lemma cancel_all_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and ct_not_blocked and invs\<rbrace>
   cancel_all_ipc x
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_all_ipc_def
  apply wpsimp
       apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set queue. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<and> x \<noteq> cur_thread s" in hoare_post_add)
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
      apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set queue. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<and> x \<noteq> cur_thread s" in hoare_post_add)
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
     apply (clarsimp simp: obj_at_def)
     apply (subgoal_tac "ipc_queued_thread xaa s")
      apply (subgoal_tac "(xaa \<noteq> cur_thread s)")
       apply (clarsimp simp: obj_at_kh_kheap_simps cur_sc_chargeable_def pred_map_simps, fastforce)
      apply (clarsimp simp: obj_at_kh_kheap_simps ct_in_state_kh_simp pred_map_simps)
     apply (erule sym_refs_SendEP_ipc_queued_thread; clarsimp)
    apply (clarsimp simp:  cur_sc_chargeable_def vs_all_heap_simps)
   apply (clarsimp simp: obj_at_def)
   apply (subgoal_tac "ipc_queued_thread xaa s")
    apply (subgoal_tac "(xaa \<noteq> cur_thread s)")
     apply (clarsimp simp: obj_at_kh_kheap_simps cur_sc_chargeable_def pred_map_simps, fastforce)
    apply (clarsimp simp: obj_at_kh_kheap_simps ct_in_state_kh_simp pred_map_simps)
   apply (erule sym_refs_RecvEP_ipc_queued_thread; clarsimp)
  apply (clarsimp simp:  cur_sc_chargeable_def vs_all_heap_simps)
  done

lemma cancel_all_signals_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   cancel_all_signals x
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cancel_all_signals_def
  apply wpsimp
      apply (rule_tac R="\<lambda>_ s. \<forall>x \<in> set x2. \<not> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (x) s \<and> x \<noteq> cur_thread s" in hoare_post_add)
      apply (rule mapM_x_wp[where S="set xs" and xs=xs for xs])
       apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_thread_state_csctb sts_st_tcb_at_other)
          apply (wps, wpsimp)
         apply (wps, wpsimp)
        apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_thread_state_csctb sts_st_tcb_at_other
                          possible_switch_to_ct_not_queued possible_switch_to_scheduler_act_sane')
       apply (intro conjI; clarsimp)
      apply simp
     apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)+
  apply (intro conjI)
   apply (clarsimp simp: obj_at_def)
   apply (subgoal_tac "ipc_queued_thread xaa s")
    apply (subgoal_tac "(xaa \<noteq> cur_thread s)")
     apply (clarsimp simp: obj_at_kh_kheap_simps cur_sc_chargeable_def pred_map_simps, fastforce)
    apply (clarsimp simp: obj_at_kh_kheap_simps ct_in_state_kh_simp pred_map_simps)
   apply (erule sym_refs_WaitingNtfn_ipc_queued_thread, assumption, clarsimp, clarsimp)
  apply (clarsimp simp:  cur_sc_chargeable_def vs_all_heap_simps)
  done

lemma blocked_cancel_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s) and st_tcb_at (Not \<circ> inactive) x\<rbrace>
   blocked_cancel_ipc a x c
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp wp: reply_unlink_tcb_csctb get_simple_ko_wp set_simple_ko_wp get_ep_queue_wp get_blocking_object_wp)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)
  by fastforce

lemma reply_remove_tcb_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   reply_remove_tcb x b
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding reply_remove_tcb_def
  apply (wpsimp wp: reply_unlink_tcb_csctb update_sk_obj_ref_wp update_sched_context_wp get_sk_obj_ref_wp gts_wp)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)
  by fastforce

lemma cancel_signal_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   cancel_signal x b
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_signal_def
  apply (wpsimp wp: reply_unlink_tcb_csctb set_simple_ko_wp get_simple_ko_wp)
  by (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)

lemma thread_set_cur_sc_chargeable_indep:
  "\<forall>tcb. tcb_sched_context (a tcb) = tcb_sched_context (tcb) \<Longrightarrow>
   \<forall>tcb. tcb_state (a tcb) = tcb_state tcb \<Longrightarrow>
   thread_set a b \<lbrace>cur_sc_chargeable\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def)
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
   apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps cur_sc_chargeable_def ct_in_state_def
          , fastforce)
  apply (fastforce simp: tcb_at_kh_simps vs_all_heap_simps)
  done

lemma cancel_ipc_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and cur_tcb and (\<lambda>s. x\<noteq>cur_thread s)\<rbrace>
   cancel_ipc x
   \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cancel_ipc_def
  apply (wpsimp wp: blocked_cancel_ipc_cur_sc_chargeable
                    reply_remove_tcb_cur_sc_chargeable
                    cancel_signal_cur_sc_chargeable thread_set_wp gts_wp)
  by (fastforce simp: cur_sc_chargeable_def obj_at_kh_kheap_simps vs_all_heap_simps)

crunches cancel_ipc, reply_remove, sched_context_unbind_all_tcbs, suspend, unbind_from_sc
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps hoare_vcg_all_lift)

lemma fast_finalise_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   fast_finalise d e
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac d; simp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_cur_sc_chargeable)
    apply (wpsimp wp: cancel_all_signals_cur_sc_chargeable unbind_maybe_notification_invs simp:)
   subgoal for rcap
   apply (wpsimp wp: cancel_ipc_cur_sc_chargeable reply_remove_cur_sc_chargeable)
     apply (wpsimp wp: gts_wp get_simple_ko_wp)+
   apply (subgoal_tac "st_tcb_at (ipc_queued_thread_state) x s")
    apply (clarsimp simp: obj_at_kh_kheap_simps ct_in_state_kh_simp)
   apply (intro conjI; intro allI impI; clarsimp simp: invs_def pred_map_simps)
   apply (subgoal_tac "(rcap, TCBReply) \<in> state_refs_of s x")
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                          pred_neg_def
                   split: thread_state.splits if_splits)
   apply (erule reply_tcb_not_idle_thread_helper, simp add: obj_at_def, clarsimp)
   done
  apply (wpsimp simp: )
  done

lemma cap_delete_one_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   cap_delete_one d
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: get_cap_wp fast_finalise_cur_sc_chargeable)

lemma suspend_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and ct_not_blocked\<rbrace>
   suspend x
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding suspend_def update_restart_pc_def
  by (wpsimp wp: set_tcb_obj_ref_cur_sc_chargeable_const hoare_drop_imp
                    cancel_ipc_cur_sc_chargeable2)

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

lemma deleting_irq_handler_cur_sc_chargeable[wp]:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   deleting_irq_handler x12
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by wpsimp

crunches finalise_cap
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma finalise_cap_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   finalise_cap d f
   \<lbrace>\<lambda>_. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (case_tac d; simp)
               apply wpsimp
              apply wpsimp
             apply (wpsimp wp: cancel_all_ipc_cur_sc_chargeable split: if_split)
             apply (wpsimp wp: cancel_all_signals_cur_sc_chargeable unbind_maybe_notification_invs split: if_split)
           apply (wpsimp wp: reply_remove_cur_sc_chargeable cancel_ipc_cur_sc_chargeable
                             gts_wp get_simple_ko_wp split: if_split)
   apply (rename_tac r R s ntfn x st)
   apply (subgoal_tac "st_tcb_at (ipc_queued_thread_state) x s")
    apply (clarsimp simp: obj_at_kh_kheap_simps ct_in_state_kh_simp)
   apply (intro conjI; intro allI impI; clarsimp simp: invs_def pred_map_simps)
           apply (subgoal_tac "(r, TCBReply) \<in> state_refs_of s x")
            apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                                  pred_neg_def
                           split: thread_state.splits if_splits)
           apply (erule reply_tcb_not_idle_thread_helper, simp add: obj_at_def, clarsimp)
          apply wpsimp
         apply (wpsimp simp: wp: suspend_cur_sc_chargeable split: if_split)
        apply wpsimp
       apply (wpsimp split: if_split simp:)
      apply (wpsimp)+
  done

lemma set_tcb_pred_tcb_const:
  "(\<And>tcb. P (proj (tcb_to_itcb (f (\<lambda>y. v) tcb))) = P (proj (tcb_to_itcb tcb))) \<Longrightarrow>
   set_tcb_obj_ref f x v \<lbrace>\<lambda>s. Q (pred_tcb_at proj P p s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (erule back_subst[where P=Q])
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemmas set_tcb_obj_ref_budget_ready_indep = set_tcb_pred_tcb_const
                                            set_tcb_budget_sufficient_const
                                            set_tcb_active_sc_tcb_at_const
                                            set_tcb_obj_ref_budget_ready_const

lemma rec_del_scheduler_act_sane[wp]:
  "rec_del call \<lbrace>scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: rec_del_preservation preemption_point_inv)

crunches cap_delete
  for simple_sched_action[wp]: "simple_sched_action :: 'state_ext state \<Rightarrow> _"
  (wp: preemption_point_inv)

lemma ct_in_state_kh_lift:
  "f \<lbrace>\<lambda>s. pred_map P (tcb_sts_of s) (cur_thread s)\<rbrace>
   \<Longrightarrow> f \<lbrace>\<lambda>s. ct_in_state P s\<rbrace>"
  by (clarsimp simp: ct_in_state_kh_simp)

lemma rec_del_ct_not_in_release_q[wp]:
  "rec_del call \<lbrace>ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: rec_del_preservation preemption_point_inv)

lemma restart_thread_if_no_fault_ct_not_queued[wp]:
 "\<lbrace>ct_not_queued and scheduler_act_sane and (\<lambda>s. tptr \<noteq> cur_thread s) and tcb_at tptr\<rbrace>
  restart_thread_if_no_fault tptr
  \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp simp: set_thread_state_def set_thread_state_act_def
               wp: possible_switch_to_ct_not_queued set_scheduler_action_wp is_schedulable_wp
                   set_object_wp thread_get_wp
                   hoare_vcg_imp_lift' )

lemma fast_finalise_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and invs and ct_not_blocked\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap)
               apply (wpsimp wp: gts_wp get_simple_ko_wp cancel_all_ipc_ct_not_queued
                                 cancel_all_signals_ct_not_queued unbind_maybe_notification_invs)+
  done

lemma deleting_irq_handler_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and invs and ct_not_blocked\<rbrace>
   deleting_irq_handler irq
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding deleting_irq_handler_def
  by (wpsimp simp: cap_delete_one_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma finalise_cap_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane and invs and ct_not_blocked\<rbrace>
   finalise_cap cap param_b
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (case_tac cap)
               apply (wpsimp wp: gts_wp get_simple_ko_wp cancel_all_ipc_ct_not_queued
                                 cancel_all_signals_ct_not_queued unbind_maybe_notification_invs
                      | clarsimp simp: split: if_split)+
  done

crunches cap_swap_for_delete, empty_slot
  for ct_not_blocked[wp]: "ct_not_blocked :: 'state_ext state \<Rightarrow> _"
  (simp: cap_swap_ext_def wp: dxo_wp_weak)

end

lemma ct_in_state_def2: "ct_in_state test s = st_tcb_at test (cur_thread s) s"
   by (simp add: ct_in_state_def)

crunches reorder_ntfn, reorder_ep
  for valid_sched[wp]:"valid_sched"
  and simple_sched_action[wp]: simple_sched_action
  (wp: mapM_wp' get_simple_ko_wp)

lemma thread_set_priority_valid_sched_misc[wp]:
  "thread_set_priority p t
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
          (scheduler_action s) (last_machine_time_of s) (tcb_sts_of s) (tcb_scps_of s)
          (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>"
  apply (wpsimp simp: thread_set_priority_def  wp: thread_set_wp)
  by (clarsimp simp: obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps)

lemma thread_set_domain_valid_sched_misc[wp]:
  "thread_set_domain t d
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s) (release_queue s)
          (scheduler_action s) (last_machine_time_of s) (tcb_sts_of s) (tcb_scps_of s)
          (tcb_faults_of s) (sc_refill_cfgs_of s) (sc_replies_of s)\<rbrace>"
  apply (wpsimp simp: thread_set_domain_def  wp: thread_set_wp)
  by (clarsimp simp: obj_at_kh_kheap_simps fun_upd_def vs_all_heap_simps)

lemma thread_set_domain_st_tcb[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (st_tcb_at Q p s)\<rbrace>"
  by (clarsimp simp: tcb_at_kh_simps, wpsimp)

lemma thread_set_priority_valid_ready_qs_not_q:
  "\<lbrace>valid_ready_qs and not_queued t\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps not_queued_def dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=ta in bspec, simp, clarsimp)
  apply (rename_tac scp sc n)
  apply (rule_tac x=scp in exI; fastforce)
  done

lemma thread_set_priority_switch_in_cur_domain[wp]:
  "thread_set_priority t p \<lbrace>switch_in_cur_domain\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at'_def vs_all_heap_simps
                 dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_ct_in_cur_domain[wp]:
  "thread_set_priority p t \<lbrace>ct_in_cur_domain\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcb_at'_def vs_all_heap_simps
                 dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_valid_idle_etcb[wp]:
  "thread_set_priority t p \<lbrace>valid_idle_etcb\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp wp_del: valid_idle_etcb_lift)
  apply (clarsimp simp: valid_idle_etcb_def vs_all_heap_simps etcb_at'_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_valid_sched:
  "\<lbrace>valid_sched and not_queued t\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  by (wpsimp wp: thread_set_priority_valid_ready_qs_not_q)

lemma is_schedulable_opt_ready_queues_update[simp]:
  "is_schedulable_opt t q (ready_queues_update f s) = is_schedulable_opt t q s"
  by (clarsimp simp: is_schedulable_opt_def get_tcb_def is_sc_active_def
                  split: option.splits)

lemma ct_not_in_q_not_cur_threadE:
  "tptr \<in> set (ready_queues s d p)
   \<Longrightarrow> ct_not_in_q s
   \<Longrightarrow> not_cur_thread tptr s"
  by (clarsimp simp: ct_not_in_q_def not_cur_thread_def not_queued_def)

lemma set_priority_valid_sched:
  "\<lbrace>valid_sched and ct_released and ct_active and ct_not_in_release_q\<rbrace>
   set_priority tptr prio
   \<lbrace>\<lambda>_. valid_sched \<rbrace>"
  apply (clarsimp simp: set_priority_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_vcg_if_lift2 reschedule_required_valid_sched'
                    tcb_sched_enqueue_valid_blocked_except_set)
          apply (wpsimp wp: thread_set_priority_valid_ready_qs_not_q)
         apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                           tcb_sched_dequeue_valid_blocked_except_set_const)
        apply (wpsimp wp: thread_set_priority_valid_sched)
       apply (wpsimp wp: thread_get_wp)+
    apply (rule_tac Q="\<lambda>r. valid_sched" in hoare_strengthen_post; wpsimp wp: thread_set_priority_valid_sched)
   apply (rule_tac Q="\<lambda>r. valid_sched" in hoare_strengthen_post; wpsimp wp: thread_set_priority_valid_sched)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def obj_at_def)
  apply (intro conjI; intro impI)
   apply (frule pred_tcb_at_tcb_at, clarsimp simp: obj_at_def is_tcb)
   apply (intro conjI; intro impI)
     apply (clarsimp simp: valid_ready_qs_def valid_blocked_thread_def tcb_at_kh_simps
                           released_sc_tcb_at_def)
     apply (fastforce simp: not_queued_def ready_or_release_2_def)
    apply (intro conjI)
     apply (clarsimp simp: valid_blocked_thread_def ct_in_state_def runnable_eq_active)
    apply (clarsimp simp: valid_ready_qs_def valid_blocked_thread_def tcb_at_kh_simps
                          released_sc_tcb_at_def)
   apply (clarsimp simp: vs_all_heap_simps valid_ready_qs_def in_ready_q_def tcb_at_kh_simps
          , fastforce)
  apply (clarsimp simp: vs_all_heap_simps valid_ready_qs_def in_ready_q_def tcb_at_kh_simps
         , fastforce)
  done

lemma set_mcpriority_valid_sched_pred_strong[wp]:
  "set_mcpriority tptr prio \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

lemma set_priority_simple_sched_action[wp]:
  "set_priority param_a param_b \<lbrace>simple_sched_action\<rbrace>"
  unfolding set_priority_def
  by (wpsimp simp: get_thread_state_def thread_get_def wp: maybeM_inv)

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

lemma sched_context_resume_cond_budget_ready_sufficient:
  "\<lbrace>bound_sc_tcb_at (\<lambda>a. a = Some sc_ptr) tcbptr
    and sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>rv s. st_tcb_at runnable tcbptr s \<and> active_sc_tcb_at tcbptr s \<and> not_in_release_q tcbptr s
           \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_resume_def
  apply wpsimp
              apply (rule_tac Q="\<lambda>r. in_release_queue tcbptr" in hoare_strengthen_post[rotated])
               apply (clarsimp simp: in_release_queue_def not_in_release_q_def)
              apply (wpsimp simp: in_release_queue_in_release_q
                              wp: postpone_in_release_q)+
           apply (wpsimp wp: thread_get_wp' is_schedulable_wp')+
  apply (auto simp: sc_at_pred_n_eq_commute sc_tcb_sc_at_def obj_at_kh_kheap_simps
                    vs_all_heap_simps)
  done

lemma sc_tcb_update_sc_tcb_sc_at:
  "\<lbrace>K (P t)\<rbrace> set_sc_obj_ref sc_tcb_update sc t \<lbrace>\<lambda>rv. sc_tcb_sc_at P sc\<rbrace>"
  apply (wpsimp simp: wp: update_sched_context_wp)
  by (clarsimp simp: obj_at_def sc_at_pred_n_def)

lemma set_tcb_sched_context_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
        \<and> (\<forall>scp. sco = Some scp \<longrightarrow> sched_context_donate_ipc_queues_precond t scp s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t sco
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  apply (wpsimp wp: valid_sched_wp)
  by (cases sco; clarsimp simp: is_blocked_thread_state_defs vs_all_heap_simps elim!: released_ipc_queuesE split: if_splits)

lemmas sched_context_resume_st_tcb_at'[wp]
  = sched_context_resume_st_tcb_at[unfolded obj_at_kh_kheap_simps]

lemma sched_context_bind_tcb_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> simple_sched_action s
        \<and> pred_map_eq None (tcb_scps_of s) tcbptr
        \<and> not_cur_thread tcbptr s
        \<and> sched_context_donate_ipc_queues_precond tcbptr scptr s\<rbrace>
   sched_context_bind_tcb scptr tcbptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: sched_context_bind_tcb_def)
  apply (wpsimp wp: is_schedulable_wp' reschedule_valid_sched_const)
     apply (rule_tac Q="\<lambda>r s. valid_sched_except_blocked s
                              \<and> valid_blocked_except tcbptr s
                              \<and> not_cur_thread tcbptr s
                              \<and> (st_tcb_at runnable tcbptr s\<and> active_sc_tcb_at tcbptr s \<and> not_in_release_q tcbptr s
                                 \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)"
                     in hoare_strengthen_post[rotated])
      apply (clarsimp simp: valid_sched_valid_sched_except_blocked obj_at_kh_kheap_simps runnable_eq_active
                     elim!: valid_blockedE' split: if_splits)
     apply (wpsimp wp: sched_context_resume_valid_sched_except_blocked
                       sched_context_resume_cond_budget_ready_sufficient)
    apply (rule_tac Q="\<lambda>r. valid_sched_except_blocked and
                           valid_blocked_except_set {tcbptr} and
                           not_cur_thread tcbptr and
                           sc_tcb_sc_at ((=) (Some tcbptr)) scptr and
                           bound_sc_tcb_at (\<lambda>a. a = Some scptr) tcbptr"
                    in hoare_strengthen_post[rotated])
     apply (clarsimp simp: sc_at_pred_n_eq_commute)
     apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps heap_refs_retract_at_def)
    apply (wpsimp wp: set_tcb_sched_context_valid_ready_qs_not_queued
                      set_tcb_sched_context_valid_release_q_not_queued
                      set_tcb_sched_context_simple_valid_sched_action
                      set_tcb_sched_context_Some_valid_blocked_except
                      set_tcb_sched_context_released_ipc_queues
                      ssc_bound_sc_tcb_at
           simp: valid_sched_def)
   apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_disj_lift sc_tcb_update_sc_tcb_sc_at simp: pred_neg_def)
  apply (clarsimp simp: valid_sched_def cong: conj_cong)
  apply (intro conjI)
   apply (simp add: valid_ready_qs_def not_queued_def released_sc_tcb_at_def pred_tcb_at_def
                    obj_at_def vs_all_heap_simps is_blocked_thread_state_defs
          , fastforce)
  apply (simp add: valid_release_q_def not_in_release_q_def pred_tcb_at_def obj_at_def
                   vs_all_heap_simps
         , fastforce)
  done

lemma maybe_sched_context_bind_tcb_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> simple_sched_action s \<and> bound_sc_tcb_at ((=) None) tcbptr s \<and> not_cur_thread tcbptr s
        \<and> sched_context_donate_ipc_queues_precond tcbptr scptr s\<rbrace>
   maybe_sched_context_bind_tcb scptr tcbptr
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  unfolding maybe_sched_context_bind_tcb_def
  apply (wpsimp wp: sched_context_bind_tcb_valid_sched get_tcb_obj_ref_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)

context DetSchedSchedule_AI_det_ext begin

crunches install_tcb_cap
for valid_sched[wp]: "valid_sched :: det_ext state \<Rightarrow> _"
and simple_sched_action[wp]: "simple_sched_action :: det_ext state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv simp: crunch_simps)

lemma install_tcb_frame_cap_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and invs\<rbrace> install_tcb_frame_cap a d f \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_frame_cap_def
  by (wpsimp wp: reschedule_valid_sched_const check_cap_inv hoare_drop_imp
                 thread_set_not_state_valid_sched)

end

crunch scheduler_act_not[wp]: set_priority "scheduler_act_not y"
  (wp: crunch_wps simp: crunch_simps)

crunches reorder_ntfn
  for valid_sched_pred[wp]: "valid_sched_pred_strong P"
  (wp: crunch_wps simp: crunch_simps ignore: set_simple_ko)

crunches reorder_ep
  for valid_sched_pred[wp]:
   "\<lambda>s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunches set_priority, set_mcpriority
  for interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_priority_valid_sched_misc[wp]:
  "set_priority tptr prio
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s) (cur_time s) (cur_domain s) (cur_thread s)
          (idle_thread s) (release_queue s) (last_machine_time_of s)
          (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)
          (sc_replies_of s)\<rbrace>"
  by (wpsimp wp: thread_get_wp gts_wp
           simp: get_tcb_queue_def obj_at_def st_tcb_at_def is_tcb_def set_priority_def)

lemma set_priority_bound_sc_tcb_at_cur_thread[wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   set_priority param_a param_b
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at bound (cur_thread s) s\<rbrace>"
  by (rule_tac f="cur_thread" in hoare_lift_Pf;
      wpsimp simp: set_priority_def get_thread_state_def thread_get_def thread_set_priority_def
               wp: maybeM_inv reschedule_required_lift)

crunch simple_sched_action[wp]: sched_context_bind_tcb simple_sched_action
  (wp: crunch_wps simp: crunch_simps)

lemma set_mcpriority_bound_sc_tcb_at_cur_thread[wp]:
  "set_mcpriority target a \<lbrace>(\<lambda>s. bound_sc_tcb_at P (cur_thread s) s)\<rbrace>"
  unfolding set_mcpriority_def
  apply (wpsimp simp: thread_set_def wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

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

context DetSchedSchedule_AI_det_ext begin

lemma tcc_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf (ThreadControlCaps target slot fault_handler timeout_handler
                                      croot vroot buffer)
    and ct_active and ct_released\<rbrace>
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

crunches cancel_all_ipc
  for active_sc_tcb_at[wp]: "(\<lambda>s. P (active_sc_tcb_at t s)):: det_state \<Rightarrow> _"
  and budget_ready[wp]: "(\<lambda>s. P (budget_ready t s)):: det_state \<Rightarrow> _"
  and budget_sufficient[wp]: "(\<lambda>s. P (budget_sufficient t s)):: det_state \<Rightarrow> _"
  and released_sc_at[wp]: "(\<lambda>s. P (released_sc_at sc s)):: det_state \<Rightarrow> _"
  and is_active_sc[wp]: "(\<lambda>s. P (is_active_sc sc s)):: det_state \<Rightarrow> _"
  and released_sc_tcb_at[wp]: "(\<lambda>s. P (released_sc_tcb_at sc s)):: det_state \<Rightarrow> _"
  and not_in_release_q[wp]: "(\<lambda>s. not_in_release_q t s):: det_state \<Rightarrow> _"
  and timeout_faulted_tcb_at[wp]: "(\<lambda>s. P (timeout_faulted_tcb_at sc s)):: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma restart_thread_if_no_fault_ct_in_state_neq:
  "\<lbrace>ct_in_state P and (\<lambda>s. t \<noteq> cur_thread s \<or> (P Inactive \<and> P Restart))\<rbrace>
   restart_thread_if_no_fault t
  \<lbrace>\<lambda>_. ct_in_state P :: det_state \<Rightarrow> _\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp wp: sts_ctis_neq simp: thread_get_def)

lemma reply_unlink_tcb_ct_in_state_neq:
  "\<lbrace>ct_in_state P and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
   reply_unlink_tcb t r
  \<lbrace>\<lambda>_. ct_in_state P :: det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: sts_ctis_neq gts_wp get_simple_ko_wp)

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

lemma install_tcb_cap_released_sc_at[wp]:
  "\<lbrace>invs and tcb_at target and released_sc_at sc \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. released_sc_at sc :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_is_active_sc[wp]:
  "\<lbrace>invs and tcb_at target and is_active_sc sc \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. is_active_sc sc :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_released_sc_tcb_at[wp]:
  "\<lbrace>invs and tcb_at target and released_sc_tcb_at t \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. released_sc_tcb_at t :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_ct_active:
  "\<lbrace>invs and tcb_at target and ct_active\<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. ct_active :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  apply wpsimp
  apply (wpsimp wp: check_cap_inv )
  apply (simp)
  apply (rule valid_validE, rule cap_delete_fh_lift)
  by wpsimp+

lemma install_tcb_cap_not_ipc_queued_thread[wp]:
  "\<lbrace>tcb_at target and not_ipc_queued_thread target and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_. not_ipc_queued_thread target\<rbrace>"
  apply (simp add: tcb_at_kh_simps[symmetric])
  apply wp_pre
   apply (rule hoare_strengthen_post, rule install_tcb_cap_not_ipc_queued_thread)
   apply (simp add: not_pred_tcb_at_strengthen)
  apply (simp add: not_pred_tcb pred_neg_def)
  done

lemma install_tcb_cap_not_in_release_q[wp]:
  "\<lbrace>invs and tcb_at target and not_in_release_q t\<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_. not_in_release_q t :: det_state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

lemma install_tcb_cap_timeout_faulted_tcb_at:
  "\<lbrace>invs and tcb_at target and (\<lambda>s. P (timeout_faulted_tcb_at t s)) \<rbrace>
   install_tcb_cap target slot 3 slot_opt
  \<lbrace>\<lambda>_ s:: det_state. P (timeout_faulted_tcb_at t s)\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift)

(* FIXME RT: move? *)
lemma install_tcb_cap_not_is_blocked_thread_states[wp]:
  "\<not> (P Restart) \<Longrightarrow> \<not> (P Inactive) \<Longrightarrow>
   \<lbrace>st_tcb_at (not P) target and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_. st_tcb_at (not P) target\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_fh_lift cancel_all_ipc_st_tcb_at
           simp: pred_neg_def)+

lemma install_tcb_cap_blocked_on_recv_ntfn_tcb_at[wp]:
  "\<lbrace>tcb_at target and (\<lambda>s. \<not> blocked_on_recv_ntfn_tcb_at target s) and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_ s. \<not> blocked_on_recv_ntfn_tcb_at target s\<rbrace>"
  apply (simp add: tcb_at_kh_simps[symmetric])
  apply wp_pre
   apply (rule hoare_strengthen_post)
    apply (rule install_tcb_cap_not_is_blocked_thread_states[where P="is_blocked_on_recv_ntfn", simplified])
   apply (simp add: not_pred_tcb_at_strengthen)
  apply (simp add: not_pred_tcb pred_neg_def)
  done

lemma install_tcb_cap_blocked_on_send_tcb_at[wp]:
  "\<lbrace>tcb_at target and (\<lambda>s. \<not> blocked_on_send_tcb_at target s) and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_ s. \<not> blocked_on_send_tcb_at target s\<rbrace>"
  apply (simp add: tcb_at_kh_simps[symmetric])
  apply wp_pre
   apply (rule hoare_strengthen_post)
    apply (rule install_tcb_cap_not_is_blocked_thread_states[where P="is_blocked_on_send", simplified])
   apply (simp add: not_pred_tcb_at_strengthen)
  apply (simp add: not_pred_tcb pred_neg_def)
  done

lemma install_tcb_cap_blocked_on_reply_tcb_at[wp]:
  "\<lbrace>tcb_at target and (\<lambda>s. \<not> blocked_on_reply_tcb_at target s) and invs\<rbrace>
   install_tcb_cap target slot 3 slot_opt
   \<lbrace>\<lambda>_ s. \<not> blocked_on_reply_tcb_at target s\<rbrace>"
  apply (simp add: tcb_at_kh_simps[symmetric])
  apply wp_pre
   apply (rule hoare_strengthen_post)
    apply (rule install_tcb_cap_not_is_blocked_thread_states[where P="is_blocked_on_reply", simplified])
   apply (simp add: not_pred_tcb_at_strengthen)
  apply (simp add: not_pred_tcb pred_neg_def)
  done

lemma tcs_valid_sched:
  "\<lbrace>valid_sched and invs and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf (ThreadControlSched target slot fault_handler mcp priority sc)
    and ct_active and ct_released and ct_not_in_release_q\<rbrace>
     invoke_tcb (ThreadControlSched target slot fault_handler mcp priority sc)
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (simp add: split_def cong: option.case_cong)
  apply (wp maybeM_wp_drop_None)
      \<comment> \<open>bind/unbind sched context\<close>
      apply (clarsimp cong: conj_cong)
      apply (wpsimp wp: maybe_sched_context_bind_tcb_valid_sched
                        maybe_sched_context_unbind_tcb_valid_sched, assumption)
     apply (strengthen not_cur_thread_2_simps)
     \<comment> \<open>set priority\<close>
     apply (clarsimp cong: conj_cong)
     apply (rule hoare_post_add[where R="\<lambda>_.valid_sched and simple_sched_action"])
     apply (clarsimp cong: conj_cong)
     apply (wp maybeM_wp_drop_None)
     apply (wpsimp wp: set_priority_valid_sched hoare_vcg_all_lift hoare_vcg_imp_lift)
     apply assumption
    \<comment> \<open>set mcpriority\<close>
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift )
   \<comment> \<open>install_tcb_cap\<close>
   apply (clarsimp cong: conj_cong)
   apply (rule hoare_vcg_E_elim, wpsimp)
   apply (rule valid_validE_R)
   apply ((wpsimp wp: hoare_vcg_all_lift install_tcb_cap_ct_active
                      hoare_vcg_imp_lift install_tcb_cap_timeout_faulted_tcb_at
                  split: if_split
         | rule valid_validE, wps)+)[1]
  \<comment> \<open>resolve using preconditions\<close>
  apply (simp add: obj_at_kh_kheap_simps pred_map_ipc_queued_thread_state_iff split: option.splits;
         fastforce simp add:  pred_map_def pred_map_weakenE)
  done

end

crunch not_cur_thread[wp]: reply_remove "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma possible_switch_to_ready_or_release[wp]:
  "possible_switch_to thread \<lbrace>ready_or_release\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  done

lemma awaken_valid_sched_helper:
  shows
  "\<lbrace>valid_sched_except_blocked and K (distinct queue) and (\<lambda>s. idle_thread s \<notin> set queue)
   and valid_blocked_except_set (set queue) and (\<lambda>s. cur_thread s \<notin> set queue)
   and (\<lambda>s. \<forall>target \<in> set queue. ((st_tcb_at runnable target
                and active_sc_tcb_at target and not_in_release_q target and
                budget_ready target and budget_sufficient target) s ))\<rbrace>
                      mapM_x (\<lambda>t. do consumed <- gets consumed_time;
                             sc_opt <- thread_get tcb_sched_context t;
                             scp <- assert_opt sc_opt;
                             sufficient <- get_sc_refill_sufficient scp consumed;
                             assert sufficient;
                             possible_switch_to t;
                             modify (reprogram_timer_update (\<lambda>_. True))
                          od) queue
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  supply possible_switch_to_ct_not_in_q[wp]
  apply (induct queue; clarsimp simp: mapM_append_single mapM_x_Nil mapM_x_Cons bind_assoc)
   apply (wpsimp simp: valid_sched_def)
  apply (wpsimp simp: valid_sched_def thread_get_def
                  wp: possible_switch_to_valid_ready_qs assert_inv
                      possible_switch_to_valid_blocked
                      hoare_vcg_ball_lift)
  apply (clarsimp simp: valid_sched_def released_sc_tcb_at_def)
  apply (fastforce simp: tcb_at_kh_simps(2))
  done

lemma dropWhile_takeWhile_distinct:
  "distinct xs \<Longrightarrow> a \<in> set (dropWhile P xs) \<Longrightarrow> a \<in> set (takeWhile P xs) \<Longrightarrow> False"
  apply (subst (asm) takeWhile_dropWhile_id[symmetric, where P=P])
  apply (subst (asm) distinct_append)
  by fastforce

lemma sorted_wrt_sublist:
  "\<lbrakk>sorted_wrt P ls; sublist xs ls\<rbrakk> \<Longrightarrow> sorted_wrt P xs"
  apply (subst sorted_wrt_iff_nth_less)
  by (clarsimp simp: sorted_wrt_append sorted_wrt_nth_less sublist_def)

lemma dropWhile_sublist:
  "sublist (dropWhile P xs) xs"
  by (induct xs rule: list.induct; simp add: sublist_Cons_right)+

lemma valid_release_q_2_dropWhile:
  "valid_release_q_2 rq1 states scps refills
   \<Longrightarrow> valid_release_q_2 (dropWhile P rq1) states scps refills"
  unfolding valid_release_q_def
  apply simp
  apply (intro conjI)
  apply (clarsimp dest!: set_dropWhileD)
  apply (simp add: sorted_release_q_def)
  apply (elim conjE)
  using sorted_wrt_sublist dropWhile_sublist by fast

lemma valid_sched_action_2_subset_eq:
  "set (rlq') \<subseteq> set (rlq)
   \<Longrightarrow> valid_sched_action_2 wk_vsa except curtime sa ct cdom rlq etcbs tcb_sts tcb_scps sc_refill_cfgs
   \<Longrightarrow> valid_sched_action_2 wk_vsa except curtime sa ct cdom rlq' etcbs tcb_sts tcb_scps sc_refill_cfgs"
  unfolding valid_sched_action_def
  by (fastforce simp: weak_valid_sched_action_def)

lemma valid_blocked_except_set_dropWhile_rlq:
  "distinct rlq
   \<Longrightarrow> valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
   \<Longrightarrow> valid_blocked_except_set_2 (except \<union> set (takeWhile P rlq)) queues (dropWhile P rlq) sa ct tcb_sts tcb_scps sc_refill_cfgs"
  unfolding valid_blocked_except_set_2_def
  apply (clarsimp simp: valid_blocked_thread_def)
  apply (drule_tac x=t in spec, clarsimp)
  apply (clarsimp simp: not_in_release_q_2_def in_queue_2_def)
  apply (subgoal_tac "t \<in> set (takeWhile P rlq @ dropWhile P rlq)")
   apply (subst (asm) set_append, clarsimp)
  apply clarsimp
  done

lemmas valid_blocked_dropWhile_rlq = valid_blocked_except_set_dropWhile_rlq[where except="{}", simplified]


(* valid_refills *)

lemma valid_refills_refills_sum:
  "valid_refills scp s \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
       \<and> refills_sum (sc_refills sc) = sc_budget sc) scp s"
  by (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps sc_valid_refills_def)

lemma valid_refills_sc_refill_max:
  "valid_refills scp s \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                        \<and> length (sc_refills sc) \<le> sc_refill_max sc) scp s"
  by (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps valid_refills_def)

lemma sc_valid_refills_refills_sum:
  "sc_valid_refills sc \<Longrightarrow> refills_sum (sc_refills sc) = sc_budget sc"
  by (clarsimp simp: sc_valid_refills_def)

lemma valid_refills_consumed_time_update[iff]:
  "valid_refills p (consumed_time_update f s) = valid_refills p s"
  by (simp add: )

lemma sc_valid_refills_unat_sum_list_at_most_unat_max_word:
  "\<lbrakk>sc_valid_refills sc;
    MIN_SC_BUDGET \<le> sc_budget sc\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount (sc_refills sc))) \<le> unat max_time"
  apply (rule unat_sum_list_at_most_unat_max_word)
      apply (simp add: sc_valid_refills_def)+
   apply (elim conjE)
   apply (metis MIN_BUDGET_pos gr0I unat_eq_zero word_le_less_eq word_not_simps(1))
  apply (simp add: sc_valid_refills_def refills_sum_def)
  using MIN_BUDGET_le_MIN_SC_BUDGET by force

lemma valid_refills_refills_unat_sum_equals_budget:
  "\<lbrakk>sc_valid_refills sc;
    MIN_SC_BUDGET \<le> sc_budget sc\<rbrakk>
   \<Longrightarrow> sum_list (map unat (map r_amount (sc_refills sc))) = unat (sc_budget sc)"
  supply map_map [simp del]
  apply (simp add: sc_valid_refills_def; elim conjE)
  apply (rule_tac s="refills_sum (sc_refills sc)" and t="sc_budget sc" in subst; assumption?)
  apply (rule unat_sum_list_equals_budget; fastforce?)
  apply (metis MIN_BUDGET_pos unat_eq_zero word_le_less_eq word_not_simps(1))
  using MIN_BUDGET_le_MIN_SC_BUDGET by force

lemma valid_refills_scheduler_action_update[iff]:
  "valid_refills p (scheduler_action_update f s) = valid_refills p s"
  by (simp add: )

lemma valid_refills_ready_queues_update[iff]:
  "valid_refills p (ready_queues_update f s) = valid_refills p s"
  by (simp add: )

lemma valid_refills_release_queue_update[iff]:
  "valid_refills p (release_queue_update f s) = valid_refills p s"
  by (simp add: )

lemma valid_refills_kheap_tcb_update[iff]:
  "tcb_at t s \<Longrightarrow> valid_refills p (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = valid_refills p s"
  by (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps is_tcb)

lemma valid_refills_exst [iff]:
  "valid_refills p (trans_state f s) = valid_refills p s"
  by (simp add: valid_state_def)

lemma valid_refills_reprogram_timer_update [iff]:
  "valid_refills p (reprogram_timer_update f s) = valid_refills p s"
  by (simp add: valid_state_def)

lemma postpone_valid_sched_misc[wp]:
  "postpone t \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                     (idle_thread s) (scheduler_action s) (last_machine_time_of s)
                     (kheap s)\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: hoare_drop_imp)

lemma sched_context_resume_valid_sched_misc[wp]:
  "sched_context_resume sc_ptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (scheduler_action s) (last_machine_time_of s) (kheap s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imp simp: sched_context_resume_def)

lemma update_sched_context_valid_refills_no_budget_update_const:
  "\<lbrace>valid_refills scptr
    and K (scptr=p \<longrightarrow> sc_valid_refills newsc)\<rbrace>
   update_sched_context p (\<lambda>_. newsc)
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps)

lemma update_sched_context_valid_refills:
  "\<lbrace>valid_refills scptr
    and K (sc_valid_refills newsc)\<rbrace>
   update_sched_context p (\<lambda>_. newsc)
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps)

lemma update_sched_context_valid_refills':
  "\<lbrace>K (sc_valid_refills newsc)\<rbrace>
   update_sched_context p (\<lambda>_. newsc)
   \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps)

lemma update_sched_context_valid_refills_no_budget_update:
  "\<lbrace>valid_refills scptr
    and K (\<forall>sc. sc_valid_refills sc \<longrightarrow> sc_valid_refills (f sc))\<rbrace>
   update_sched_context p f
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps obj_at_def)

lemma refill_new_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. unat (cur_time s) + unat period \<le> unat max_time)
    and (\<lambda>s. if scptr \<noteq> p then valid_refills scptr s else \<exists>sc n. ko_at (SchedContext sc n) p s)
    and K (MIN_REFILLS \<le> max_refills \<and> budget \<le> period \<and> MIN_SC_BUDGET \<le> budget \<and> period \<le> MAX_SC_PERIOD)\<rbrace>
   refill_new p max_refills budget period
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  apply (wpsimp simp: refill_new_def update_sched_context_def set_refills_def is_round_robin_def
                  wp: set_object_wp get_object_wp get_sched_context_wp)
  apply (clarsimp simp: refills_sum_def obj_at_def MIN_REFILLS_def vs_all_heap_simps
                        ordered_disjoint_def no_overflow_def
                        window_def sc_valid_refills_def)
   apply (simp add: word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET)
  using word_le_nat_alt by fastforce

lemma refill_update_valid_refills[wp]:
  "\<lbrace>(\<lambda>s. unat (cur_time s) + 2 * unat new_period \<le> unat max_time)
    and (\<lambda>s. p = scptr \<longrightarrow> (\<exists>sc n. obj_at (\<lambda>ko. ko = SchedContext sc n
                \<and> unat (r_time (refill_hd sc)) + unat new_period \<le> unat max_time) p s))
    and valid_refills scptr
    and K (MIN_REFILLS \<le> new_max_refills \<and> MIN_SC_BUDGET \<le> new_budget  \<and> new_period \<le> MAX_SC_PERIOD
           \<and> new_budget \<le> new_period)\<rbrace>
   refill_update p new_period new_budget new_max_refills
   \<lbrace>\<lambda>_. valid_refills scptr\<rbrace>"
  supply if_split [split del]
  unfolding refill_update_def
  apply (wpsimp wp: set_refills_wp get_sched_context_wp hoare_vcg_if_lift2 get_object_wp
                    update_sched_context_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI; intro impI allI)

   apply (clarsimp simp: vs_all_heap_simps split: if_split)

   apply (intro conjI; intro impI allI)
    apply (clarsimp simp: sc_valid_refills_def  MIN_REFILLS_def refills_sum_def
                          not_le not_less MIN_BUDGET_nonzero vs_all_heap_simps
                   split: if_split_asm)

        \<comment> \<open>new_budget \<le> r_amount (refill_hd sc) and scptr is refill_ready\<close>
    apply (clarsimp simp: sc_valid_refills_def valid_refills_def ordered_disjoint_def
                          no_overflow_def window_def word_le_nat_alt MIN_REFILLS_def)
    apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
  using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
    apply (simp add: word_le_nat_alt)

  \<comment> \<open>new_budget \<le> r_amount (refill_hd sc) and scptr is not refill_ready\<close>
   apply (clarsimp simp: sc_valid_refills_def valid_refills_def ordered_disjoint_def
                         no_overflow_def window_def word_le_nat_alt MIN_REFILLS_def)
   apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
  using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
   apply (simp add: word_le_nat_alt)

  apply (clarsimp simp: vs_all_heap_simps split: if_split)

  apply (intro conjI; intro impI allI)
   apply (intro conjI; intro impI allI)
    apply (clarsimp simp: sc_valid_refills_def  MIN_REFILLS_def refills_sum_def
                          not_le not_less MIN_BUDGET_nonzero vs_all_heap_simps
                   split: if_split_asm)

     \<comment> \<open>r_amount (refill_hd sc) < new_budget and unused < MIN_BUDGET\<close>
    apply (intro conjI)

       \<comment> \<open>ordered_disjoint\<close>
       apply (simp add: ordered_disjoint_def)
       apply (rename_tac sc n)
       apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                           = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
        apply clarsimp
        apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
         apply (simp add: unat_sub)
        using diff_le_mono word_le_nat_alt apply blast
        apply (simp add: word_le_nat_alt)
        apply (rule order_trans[where y="unat MIN_SC_BUDGET"])
        using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fast
        apply (simp add: word_le_nat_alt)
       apply (simp add: window_def word_le_nat_alt)
       apply (rule unat_add_lem')
       apply (subgoal_tac "unat (new_period - MIN_BUDGET) \<le> unat new_period")
        apply (simp add: max_word_def)
       apply (subgoal_tac "MIN_BUDGET \<le> new_period")
        apply (simp add: unat_sub)
       apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)

      \<comment> \<open>no_overflow\<close>
      apply (simp add: no_overflow_def)
      apply clarsimp
      apply (rename_tac sc n na)
      apply (case_tac "na=0")
       apply clarsimp
       apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
        apply (simp add: unat_sub word_le_nat_alt)
       apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)
      apply clarsimp
      apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                          = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
       apply clarsimp
       apply (subgoal_tac "MIN_BUDGET \<le> new_period")
        apply (simp add: unat_sub word_le_nat_alt)
       apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)
      apply (rule unat_add_lem')
      apply (subgoal_tac "MIN_BUDGET \<le> new_period")
       apply (simp add: unat_sub max_word_def)
      apply (meson MIN_BUDGET_le_MIN_SC_BUDGET le_trans word_le_nat_alt)

     \<comment> \<open>MIN_BUDGET\<close>
     apply clarsimp
     apply (rename_tac sc n na)
     apply (case_tac "na=0")
      apply clarsimp
      apply (simp add: word_le_nat_alt)
      apply (subgoal_tac "MIN_BUDGET \<le> new_budget")
       apply (simp add: unat_sub)
       apply (subgoal_tac "2 * unat MIN_BUDGET \<le> unat new_budget")
        apply linarith
       using unat_MIN_BUDGET_MIN_SC_BUDGET apply linarith
      using MIN_BUDGET_le_MIN_SC_BUDGET unat_MIN_BUDGET_MIN_SC_BUDGET word_le_nat_alt
      apply fastforce
     apply clarsimp

    \<comment> \<open>period_window\<close>
    apply (simp add: window_def)
    apply (rename_tac sc n)
    apply (subgoal_tac "unat (r_time (refill_hd sc) + (new_period - MIN_BUDGET))
                       = unat (r_time (refill_hd sc)) + unat (new_period - MIN_BUDGET)")
     apply clarsimp
     using word_le_nat_alt unat_sub MIN_BUDGET_le_MIN_SC_BUDGET
     apply (simp add: unat_arith_simps(1) unat_sub)
    apply (rule unat_add_lem')
    apply (subgoal_tac "unat (new_period - MIN_BUDGET) \<le> unat new_period")
     apply (simp add: max_word_def)
   using MIN_BUDGET_le_MIN_SC_BUDGET apply (meson le_trans word_le_nat_alt word_sub_le_iff)
   apply (clarsimp simp: sc_valid_refills_def  MIN_REFILLS_def refills_sum_def
                         not_le not_less MIN_BUDGET_nonzero vs_all_heap_simps
                  split: if_split_asm)
   apply (intro conjI)

  \<comment> \<open>two inconsistent cases\<close>
      apply (find_goal \<open>match premises in "new_budget < 2 * MIN_BUDGET" \<Rightarrow> \<open>-\<close>\<close>
             , force simp: MIN_SC_BUDGET_def)+

     \<comment> \<open>MIN_REFILLS\<close>
  apply (simp add: MIN_REFILLS_def)


  apply (clarsimp simp: sc_valid_refills_def  MIN_REFILLS_def refills_sum_def
                        not_le not_less MIN_BUDGET_nonzero vs_all_heap_simps
                 split: if_split_asm)
  apply (intro conjI)

  \<comment> \<open>r_amount (refill_hd sc) < new_budget and MIN_BUDGET \<le> unused\<close>

  \<comment> \<open>ordered_disjoint\<close>
     apply (simp add: ordered_disjoint_def)
     apply (rename_tac sc n)
     apply (frule order.strict_implies_order)
     apply (frule (2) refill_word_proof_helper[where larger=new_budget
              and head_time="r_time (refill_hd sc)"
              and smaller="r_amount (refill_hd sc)" for sc])
     apply clarsimp
     apply (metis Nat.add_diff_assoc add_leE le_eq_less_or_eq unat_arith_simps(1))

    \<comment> \<open>no_overflow\<close>
    apply (clarsimp simp: no_overflow_def)
    apply (rename_tac sc n na)
    apply (case_tac "na=0")
     apply (drule_tac x=0 and P="\<lambda>n. n < length (sc_refills sc)
                                       \<longrightarrow> unat (r_time (sc_refills sc ! n)) + unat (r_amount (sc_refills sc ! n))
                                            \<le> unat max_word" in spec)
     apply (simp add: hd_conv_nth max_word_def)
    apply clarsimp
    apply (frule order.strict_implies_order)
    apply (frule (2) refill_word_proof_helper[where larger=new_budget
                 and head_time="r_time (refill_hd sc)"
                 and smaller="r_amount (refill_hd sc)" for sc])
    apply (clarsimp simp: unat_sub word_le_nat_alt)

   \<comment> \<open>MIN_BUDGET\<close>
   apply clarsimp
   apply (rename_tac sc n na)
   apply (case_tac "na=0"; clarsimp simp: hd_conv_nth)

  \<comment> \<open>period_window\<close>
  apply (simp add: window_def)
  apply (frule_tac order.strict_implies_order)
  apply (frule refill_word_proof_helper[where larger=new_budget
           and head_time="r_time (refill_hd sc)"
          and smaller="r_amount (refill_hd sc)" for sc])
    apply simp
   apply blast
  apply clarsimp
  apply (simp add: unat_sub word_le_nat_alt)

  done

lemma schedule_used_sum [simp]:
  "refills_sum (schedule_used b refills new) = refills_sum (refills @ [new])"
  apply (clarsimp simp: refills_sum_def Let_def)
  apply (case_tac refills)
   apply simp
  apply simp
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "sum_list (map r_amount (butlast list)) + r_amount (last list)
                     = sum_list (map r_amount (butlast list @ [last list]))")
    prefer 2
    apply (metis (no_types, hide_lams) Groups.add_ac(2) list.simps(9) refills_sum_append
                  refills_sum_def rev_eq_Cons_iff rev_map sum_list.Cons sum_list.rev)
  by simp

lemmas unat_le_mono = word_le_nat_alt

method overflow_hammer =
  ((assumption
    | subst power_two_max_word_fold olen_add_eqv[symmetric] diff_Suc_1
    | intro add_left_mono word_sub_le le_imp_less_Suc
            iffD2[OF no_olen_add_nat] order_refl
    | erule iffD1[OF word_le_nat_alt])+)[1]


lemma valid_refills_unat_sum_list_helper_helper:
  "ordered_disjoint (list :: refill list) \<Longrightarrow>
   no_overflow list \<Longrightarrow> list \<noteq> [] \<Longrightarrow>
   (unat (r_time (hd list)) + unat (sum_list (map r_amount (list))) \<le> unat max_time)"
  unfolding refills_sum_def
  apply (induction list; simp)
  apply (subgoal_tac "ordered_disjoint list \<and> no_overflow list", clarsimp)
   apply (subst unat_add_lem', overflow_hammer)
    apply (case_tac list; simp)
     apply (clarsimp simp: ordered_disjoint_def no_overflow_def)
    apply (erule order_trans[rotated])
    apply (clarsimp simp: ordered_disjoint_def no_overflow_def, fastforce)
   apply (case_tac list; simp)
    apply (clarsimp simp: ordered_disjoint_def no_overflow_def)
   apply (erule order_trans[rotated])
   apply (clarsimp simp: ordered_disjoint_def no_overflow_def, fastforce)
  apply (auto elim: ordered_disjoint_tail no_overflow_tail)
  done

lemma valid_refills_unat_sum_list_helper:
  "ordered_disjoint (list :: refill list) \<Longrightarrow>
   no_overflow list \<Longrightarrow> list \<noteq> [] \<Longrightarrow>
   unat (r_amount (hd list)) + unat (sum_list (map r_amount (tl list))) \<le> unat max_time"
  unfolding refills_sum_def
  apply (induction list; simp)
  apply (case_tac list; simp)
   apply (clarsimp simp: ordered_disjoint_def no_overflow_def)
  apply (rule_tac y="unat (r_time a) + unat (r_amount a) + unat (sum_list (map r_amount list))" in order_trans)
   apply (clarsimp simp: ordered_disjoint_def no_overflow_def)
  apply (rule_tac y="unat (r_time (hd list)) + unat (sum_list (map r_amount list))" in order_trans)
   apply (clarsimp simp: ordered_disjoint_def no_overflow_def)
   apply (drule_tac x=0 in spec)+
   apply clarsimp
  apply (rule valid_refills_unat_sum_list_helper_helper; clarsimp elim!: ordered_disjoint_tail no_overflow_tail)
  done

lemma valid_refills_unat_sum_list:
  "ordered_disjoint (list :: refill list) \<Longrightarrow>
   no_overflow list \<Longrightarrow>
   unat (sum_list (map r_amount list)) = sum_list (map (unat \<circ> r_amount) list)"
  unfolding refills_sum_def
  apply (induction list; simp)
  apply (subst unat_add_lem', overflow_hammer)
   apply (frule valid_refills_unat_sum_list_helper, simp, simp, simp)
  apply (subgoal_tac "ordered_disjoint list \<and> no_overflow list", simp)
  apply (fastforce elim: ordered_disjoint_tail no_overflow_tail)
  done

lemma valid_refills_r_amount_bounded_sc_budget:
  "sc_valid_refills sc \<Longrightarrow> r_amount (refill_hd sc) \<le> sc_budget sc"
  apply (clarsimp simp: sc_valid_refills_def)
  apply (subst (asm) eq_commute[where b = "sc_budget x" for x], simp)
  apply (case_tac "sc_refills sc"; simp)
  apply (overflow_hammer)
  apply (drule_tac valid_refills_unat_sum_list_helper; simp add: refills_sum_def)
  done

lemma valid_refills_r_amount_bounded_max_sc_period:
  "sc_valid_refills sc \<Longrightarrow> r_amount (refill_hd sc) \<le> MAX_SC_PERIOD"
  apply (clarsimp simp: sc_valid_refills_def)
  apply (rule order_trans[rotated], assumption)
  apply (rule order_trans[rotated], assumption)
  apply (rule valid_refills_r_amount_bounded_sc_budget)
  apply (clarsimp simp: sc_valid_refills_def)
  done

(* This bound is conservative and stronger bounds may be possible
   with stronger preconditions *)
lemma schedule_used_release_time_bounded:
  "refills \<noteq> [] \<longrightarrow> r_time (hd refills) \<le> r_time new
  \<Longrightarrow> refills \<noteq> [] \<longrightarrow> r_time new - r_amount (hd refills) \<le> r_time new
  \<Longrightarrow> r_time (hd (schedule_used full refills new)) \<le> r_time new"
  apply (case_tac refills;  clarsimp simp: Let_def split: if_split)
  done

(* FIXME: replace original *)
lemma ordered_disjoint_no_overflow_implies_sorted:
  "\<lbrakk>ordered_disjoint refills;
    no_overflow refills;
    k < length refills;
    l < length refills;
    k \<le> l\<rbrakk>
   \<Longrightarrow> unat (r_time (refills ! k)) \<le> unat (r_time (refills ! l))"
  apply (case_tac "k = l", simp)
  by (frule ordered_disjoint_non_adjacent[where refills=refills and k=k and l=l]; clarsimp)

lemma sc_valid_refills_times_bounded_helper:
  "sc_valid_refills sc
  \<Longrightarrow> x \<in> set (sc_refills sc)
  \<Longrightarrow> unat (r_time x) \<le> unat (r_time (refill_tl sc)) + unat (r_amount (refill_tl sc))"
  apply (rule order_trans[OF _ le_add1])
  apply (clarsimp simp: in_set_conv_nth last_conv_nth sc_valid_refills_def)
  apply (erule (2) ordered_disjoint_no_overflow_implies_sorted, clarsimp)
  by (fastforce intro: nat_le_Suc_less_imp)

lemma sc_valid_refills_times_bounded:
  "sc_valid_refills sc
  \<Longrightarrow> unat (r_time (refill_hd sc)) + unat (sc_period sc) \<le> unat max_time
  \<Longrightarrow> x \<in> set (sc_refills sc)
  \<Longrightarrow> r_time x \<le> r_time (refill_hd sc) + sc_period sc"
  apply (frule (1) sc_valid_refills_times_bounded_helper)
  apply (clarsimp simp: sc_valid_refills_def window_def word_le_nat_alt)
  apply (subst unat_add_lem', overflow_hammer)
  apply (erule (1) order_trans[rotated])
  done

lemma sc_valid_refills_no_overflow:
  "sc_valid_refills sc
  \<Longrightarrow> x \<in> set (sc_refills sc)
  \<Longrightarrow> unat (r_time x) + unat (r_amount x) \<le> unat max_time"
  by (clarsimp simp: sc_valid_refills_def no_overflow_def in_set_conv_nth)

lemma sc_valid_refills_amounts_bounded:
  "sc_valid_refills sc
  \<Longrightarrow> x \<in> set (sc_refills sc)
  \<Longrightarrow> r_amount x \<le> sc_period sc"
  apply (clarsimp simp: sc_valid_refills_def word_le_nat_alt )
  apply (rule_tac y="unat (refills_sum (sc_refills sc))" in order_trans[rotated], clarsimp)
  apply (subst refills_sum_def)
  apply (subst valid_refills_unat_sum_list, simp, simp)
  apply (rule member_le_sum_list, simp)
  done

lemma sc_valid_refills_amounts_bounded_below:
  "sc_valid_refills sc
  \<Longrightarrow> x \<in> set (sc_refills sc)
  \<Longrightarrow> MIN_BUDGET \<le> r_amount x"
  by (clarsimp simp: sc_valid_refills_def in_set_conv_nth)

lemma sc_valid_refills_hd_in_list:
  "sc_valid_refills sc
  \<Longrightarrow> hd (sc_refills sc) \<in> set (sc_refills sc)"
  by (clarsimp simp: sc_valid_refills_def)

lemma sc_refill_ready_release_time_well_bounded:
  "kheap s p = Some (SchedContext sc n)
   \<Longrightarrow> cur_sc s = p
   \<Longrightarrow> current_time_bounded 2 s
   \<Longrightarrow> valid_refills p s
   \<Longrightarrow> sc_refill_ready (cur_time s) sc
   \<Longrightarrow> unat (r_time (refill_hd sc)) + unat MAX_SC_PERIOD + unat MAX_SC_PERIOD \<le> unat max_time"
  apply (clarsimp simp: current_time_bounded_def refill_ready_def mult_2 add.assoc[symmetric])
  apply (erule order_trans[rotated], clarsimp)
  apply (rule order_trans[OF _ unat_plus_gt])
  apply (simp add: unat_le_mono)
  done

(* FIXME: develop strategy to shorten this proof *)
(* This precondition is required so that the window of the sc never includes max_word.
   In the worst possible case, the sc will forfeit it's entire window, plus usage, in which
   case the new window will end at time_head + period + usage + period *)
lemma refill_budget_check_valid_refills[wp]:
   "\<lbrace>(\<lambda>s. \<forall>sc n. (kheap s (cur_sc s) = Some (SchedContext sc n)
                  \<longrightarrow> (sc_refill_ready (cur_time s) sc \<longrightarrow> r_amount (refill_hd sc) < usage)
                  \<longrightarrow> cur_sc_offset_ready usage s))
     and valid_refills p
     and current_time_bounded 2\<rbrace>
    refill_budget_check usage
    \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  supply if_weak_cong[cong del] if_split[split del] schedule_used.simps[simp del] map_map[simp del]
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp wp: get_object_wp set_refills_wp refill_full_wp is_round_robin_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI impI allI)

      \<comment> \<open>first branch of refill_budget_check - head overfill overrun. Reschedule in one refill\<close>
      apply (clarsimp simp: vs_all_heap_simps obj_at_def )
      apply (case_tac "p \<noteq> cur_sc s")
       apply clarsimp
      apply (clarsimp simp: sc_valid_refills_def)
      apply (rename_tac s sc n)
      apply (subgoal_tac "unat (r_time (refill_hd sc)) + unat usage + unat (sc_period sc) \<le> unat max_time")
      apply (intro conjI impI allI)
          apply (simp add: refills_sum_def ordered_disjoint_def)
         apply (simp add: no_overflow_def)
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc + usage)
                             = unat (r_time (refill_hd sc)) + unat usage + unat (sc_period sc) ")
           apply (subgoal_tac "unat (sc_budget sc) \<le> unat (sc_period sc)")
            apply (clarsimp simp: cur_sc_offset_ready_def current_time_bounded_def mult_2 add.assoc[symmetric])
            apply (erule order_trans[rotated])
            apply (rule add_mono, erule add_mono)
             apply (clarsimp simp: unat_le_mono[symmetric])
            apply (clarsimp simp: unat_le_mono[symmetric], fastforce)
           apply (clarsimp simp: unat_le_mono[symmetric])
          apply (subst add.assoc, subst add.commute[where b=usage], subst add.assoc)
          apply ((subst unat_add_lem' | overflow_hammer | simp)+)[1]
  using MIN_BUDGET_le_MIN_SC_BUDGET apply force
        apply (simp add: window_def word_le_nat_alt)
  using le_def apply fastforce
   apply (clarsimp simp: word_le_nat_alt current_time_bounded_def cur_sc_offset_ready_def
                         vs_all_heap_simps)

     \<comment> \<open>second branch of refill_budget_check - head refill consumed exactly\<close>
     apply (clarsimp simp: vs_all_heap_simps sc_valid_refills_def obj_at_def set_object_def
                           get_object_def
                    split: if_splits)

     apply (frule sc_refill_ready_release_time_well_bounded, (clarsimp simp: valid_refills_def vs_all_heap_simps)+)
     apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD")
     apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat MAX_SC_PERIOD")
     apply (intro conjI)
           apply (simp add: refills_sum_def add_ac)
           apply (case_tac "sc_refills sc", force, simp)

          \<comment> \<open>ordered_disjoint\<close>
          apply (rule_tac full=False
                      and list="tl (sc_refills sc)"
                      and new="\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                r_amount = r_amount (refill_hd sc)\<rparr>"
                       in schedule_used_ordered_disjoint)
            apply (metis ordered_disjoint_tail hd_Cons_tl)
           apply clarsimp
           apply (drule_tac x="Suc m" in spec)
           apply (elim impE)
            apply linarith
           apply (metis list.exhaust_sel nth_Cons_Suc)
          apply (clarsimp simp: Let_def split: if_splits)
          apply (simp add: window_def)
          apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                              = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
           apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
            apply clarsimp
           apply (simp add: last_tl)
          apply (rule unat_add_lem', overflow_hammer, simp)

         \<comment> \<open>no_overflow\<close>
         apply (rule schedule_used_no_overflow)
            apply (metis no_overflow_tail hd_Cons_tl)
           apply (simp add: no_overflow_def)
           apply (clarsimp simp: refill_ready_def)
          apply (subst unat_add_lem', overflow_hammer, simp, simp)
            apply clarsimp
          apply (drule_tac x="Suc m" in spec)
          apply (elim impE)
           apply linarith
          apply (metis list.exhaust_sel nth_Cons_Suc)
         apply (clarsimp simp: Let_def split: if_splits)
         apply (simp add: window_def)
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
          apply clarsimp
          apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
           apply argo
          apply (simp add: last_tl)
         apply (rule unat_add_lem', simp add: max_word_def)

       \<comment> \<open>MIN_BUDGET\<close>
        apply (subgoal_tac "sum_list (map unat (map r_amount (tl (sc_refills sc)
                                                              @ [\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                                                  r_amount = r_amount (refill_hd sc)\<rparr>])))
                            = unat (sc_budget sc)")
         apply (rule schedule_used_MIN_BUDGET)
           apply (clarsimp simp: word_le_nat_alt)
          apply (clarsimp simp: word_le_nat_alt)
         apply clarsimp
         apply (drule_tac x="Suc na" in spec)
         apply (elim impE)
          apply linarith
         apply (metis list.exhaust_sel nth_Cons_Suc)
        apply (frule unat_sum_list_equals_budget; assumption?)
          apply (metis MIN_BUDGET_nonzero unat_eq_1(1) word_le_0_iff)
         apply (simp add: refills_sum_def)
         using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
        apply (case_tac "sc_refills sc", simp, fastforce)

      \<comment> \<open>period_window\<close>
       apply (case_tac "tl (sc_refills sc)")
        apply (simp add: schedule_used.simps window_def)
        apply (rule_tac y="unat (sc_budget sc)" in order_trans)
         apply (case_tac "sc_refills sc", fast, case_tac list, fastforce, fastforce)
        using unat_arith_simps(1) apply blast
       apply (clarsimp simp: Let_def window_def schedule_used.simps split: if_splits)
       apply (intro conjI impI)

          \<comment> \<open>first of five word proofs\<close>
          apply (rule_tac y="unat (sc_budget sc)" in order_trans)
           apply (fastforce simp: hd_conv_nth)
          apply (fastforce simp: unat_arith_simps(1))

         \<comment> \<open>second of the five word proofs\<close>
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
          apply clarsimp
          apply (simp add: ordered_disjoint_def)
          apply (drule_tac x=0 in spec)
          apply (elim impE)
            apply (force simp: tail_nonempty_length)
           apply (case_tac "sc_refills sc", simp, fastforce)
          apply (rule unat_add_lem', simp add: max_word_def)

         \<comment> \<open>third of the five word proofs\<close>
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - (MIN_BUDGET - r_amount (refill_hd sc)))
                             = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                               - unat MIN_BUDGET + unat (r_amount (refill_hd sc))")
          apply clarsimp
          apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
           apply (clarsimp simp: ordered_disjoint_def)
           apply (drule_tac x=0 in spec)
           apply (elim impE)
            using hd_conv_nth apply fastforce
           using hd_conv_nth apply fastforce
          using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce
         apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - (MIN_BUDGET - r_amount (refill_hd sc)))
                             = unat (r_time (refill_hd sc) + sc_period sc)
                               - unat (MIN_BUDGET - r_amount (refill_hd sc))")
          apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                              = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
           apply clarsimp
           apply (simp add: unat_sub)
           apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
            apply (simp add: hd_conv_nth word_le_not_less)
           using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce
          apply (rule unat_add_lem', simp add: max_word_def)
         apply (metis Nat.add_0_right add_Suc_shift list.exhaust_sel list.size(4) nth_Cons_0
                      word_le_not_less zero_less_Suc)

       \<comment> \<open>fourth of the word proofs\<close>
         apply (metis Nat.add_0_right add_Suc_shift list.exhaust_sel list.size(4) nth_Cons_0
                      word_le_not_less zero_less_Suc)

       \<comment> \<open>last of the word proofs - similar to the second of the word proofs above\<close>
       apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                          = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
        apply clarsimp
        apply (simp add: ordered_disjoint_def)
        apply (drule_tac x=0 in spec)
        apply (elim impE)
         apply (simp add: tail_nonempty_length)
        apply (metis hd_Cons_tl nth_Cons_0 nth_Cons_Suc)
       apply (rule unat_add_lem', simp add: max_word_def)

      \<comment> \<open>length\<close>
      using schedule_used_non_nil neq_Nil_lengthI apply blast
     apply (subgoal_tac "length (tl (sc_refills sc)) = length (sc_refills sc) - Suc 0")
      apply (metis schedule_used_length_max Nitpick.size_list_simp(2) le_trans)
     apply simp
  apply (erule order_trans[rotated])
  apply (clarsimp simp: unat_le_mono[symmetric])
  apply (rule sc_valid_refills_amounts_bounded)
  apply (clarsimp simp: sc_valid_refills_def vs_all_heap_simps)
  apply simp
  apply (clarsimp simp: unat_le_mono[symmetric])

    \<comment> \<open>third branch of refill_budget_check - tail is empty,
         so just advance time of the single refill\<close>
    apply (clarsimp simp: vs_all_heap_simps sc_valid_refills_def obj_at_def set_object_def
                             get_object_def
                   split: if_splits)
    apply (subgoal_tac "sc_refills sc = [refill_hd sc]")
     apply (frule sc_refill_ready_release_time_well_bounded, (clarsimp simp: valid_refills_def vs_all_heap_simps)+)
     apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD")
     apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
     apply (subgoal_tac "unat usage \<le> unat (r_amount (refill_hd sc))")

    apply (intro conjI)
          apply (metis Nil_is_append_conv add.right_cancel append_Nil hd_append2 list.expand
                       list.sel(1) list.sel(3) neq_Nil_conv refills_sum_append refills_sum_cons
                       tl_append2)
        apply (simp add: ordered_disjoint_def)
       apply (simp add: no_overflow_def)
       apply (subst refill_word_proof_helper)

          apply (simp add: word_le_nat_alt)
          apply (simp add: word_le_nat_alt)
         apply simp
    apply simp
      apply (simp add: hd_conv_nth)
     apply (simp add: window_def)
     apply (simp add: word_le_nat_alt)
    apply (metis Nitpick.size_list_simp(2) length_0_conv)
  apply (clarsimp simp: unat_le_mono word_le_not_less[symmetric])
  apply (clarsimp simp: unat_le_mono[symmetric])
  apply (rule sc_valid_refills_amounts_bounded)
  apply (clarsimp simp: sc_valid_refills_def vs_all_heap_simps)
  apply simp
  apply (clarsimp simp: unat_le_mono[symmetric])
         apply (metis list.exhaust_sel)

   \<comment> \<open>fourth branch of refill_budget_check - remnant < MIN_BUDGET, so pop head,
        add remnant to second refill, and do schedule_used\<close>
   apply (clarsimp simp: vs_all_heap_simps sc_valid_refills_def obj_at_def set_object_def
                          get_object_def
                  split: if_splits)

   \<comment> \<open>we introduce some facts which will be useful both for ordered_disjoint and no_overflow\<close>
  apply (frule sc_refill_ready_release_time_well_bounded, clarsimp, clarsimp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps)
   apply (clarsimp simp: valid_refills_def vs_all_heap_simps)
  apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD")
   apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
    apply (subgoal_tac "unat usage \<le> unat (r_amount (refill_hd sc))")
    apply (frule word_le_not_less[THEN iffD2])
   apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
          ; (simp add: refills_sum_def)?)
     apply (fastforce simp: MIN_BUDGET_pos unat_gt_0)
    using MIN_BUDGET_le_MIN_SC_BUDGET apply force
   apply (frule_tac refills="sc_refills sc" in refill_word_proof_helper2[where usage=usage]
          ; fastforce?)
     apply (case_tac "sc_refills sc", fast, case_tac list, force, simp)
     apply (rule_tac y="unat (sc_budget sc)" in order_trans)
     apply linarith
     apply (simp add: word_le_nat_alt[symmetric])
    apply (metis Nitpick.size_list_simp(2) Suc_less_eq2 length_greater_0_conv)
   apply (elim conjE)
   apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                       = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
    prefer 2
    apply (rule unat_add_lem', simp add: max_word_def)
   apply (subgoal_tac "MIN_BUDGET
                       \<le> r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)")
    prefer 2
    apply (simp add: word_le_nat_alt)
    apply (frule_tac x=0 in spec)
    apply (elim impE, fastforce)
    apply (frule_tac x=1 in spec)
    apply (elim impE)
     apply (force simp: tail_nonempty_length)
    apply (simp add: hd_conv_nth)
    apply (subgoal_tac "r_amount (sc_refills sc ! Suc 0) = r_amount (tl (sc_refills sc) ! 0)")
     apply force
    apply (metis length_greater_0_conv nth_tl)
   \<comment> \<open>end of the proofs of the useful facts\<close>

   apply (intro conjI)

         \<comment> \<open>refills_sum\<close>
         apply (case_tac "sc_refills sc", fast, case_tac list, fastforce, simp add: add_ac)

       \<comment> \<open>ordered_disjoint\<close>
        apply (rule schedule_used_ordered_disjoint)
          apply (rule_tac left="[\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                  r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>]"
                      and right="tl (tl (sc_refills sc))"
                       in ordered_disjoint_append)
             apply (simp add: ordered_disjoint_def)
            apply clarsimp
            apply (erule_tac list = "sc_refills sc" and new_list="tl (tl (sc_refills sc))"
                                                     in ordered_disjoint_sublist)
            using sublist_order.order.trans apply blast
           apply (intro impI)
           apply (clarsimp simp: ordered_disjoint_def)
           apply (drule_tac x=1 in spec)
           apply (elim impE)
            using tail_nonempty_length apply force
           apply (drule_tac x=1 in spec)
           apply (elim impE)
            using tail_nonempty_length apply force
           apply (case_tac "sc_refills sc", fast, case_tac list, force, simp add: hd_conv_nth)
         apply simp
         apply clarsimp
         apply (case_tac "m=0")
          apply clarsimp
         apply (drule_tac x="m + Suc 0" in spec)
         apply (elim impE)
          apply linarith
         apply (case_tac "sc_refills sc", force, case_tac list, force, force)
        apply (intro conjI impI)
        apply (clarsimp split: if_splits)
        apply (intro conjI impI)
         apply (simp add: window_def)
         apply (subgoal_tac "refill_tl sc = hd (tl (sc_refills sc))")
          apply force
         apply (metis hd_conv_nth last_conv_nth last_tl length_tl list.size(3))
        apply (simp add: window_def)
        apply (subgoal_tac "refill_tl sc = last (tl (tl (sc_refills sc)))")
         apply argo
        apply (simp add: last_tl)

      \<comment> \<open>no_overflow\<close>
       apply (rule schedule_used_no_overflow)
          apply (rule_tac left="[\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                                       r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>]"
                                           and right="tl (tl (sc_refills sc))" in no_overflow_append)
            apply (simp add: no_overflow_def)
            apply (drule_tac x=1 in spec)
            apply (elim impE)
             using tail_nonempty_length apply force
            apply (case_tac "sc_refills sc", fast, fastforce simp: hd_conv_nth)
           apply (erule_tac list="sc_refills sc" in no_overflow_sublist)
           using sublist_order.dual_order.trans apply blast
          apply force
         apply (simp add: no_overflow_def)
        apply (clarsimp split: if_split)
        apply (case_tac "m=0")
         apply clarsimp
        apply (drule_tac x="m + Suc 0" in spec)
        apply (elim impE)
         apply linarith
        apply (case_tac "sc_refills sc", force, case_tac list, force, force)
       apply (intro conjI impI)
       apply (clarsimp split: if_splits)
       apply (intro conjI impI)
        apply (simp add: window_def)
        apply (subgoal_tac "refill_tl sc = hd (tl (sc_refills sc))")
         apply force
        apply (metis hd_conv_nth last_conv_nth last_tl length_tl list.size(3))
       apply (simp add: window_def)
       apply (subgoal_tac "refill_tl sc = last (tl (tl (sc_refills sc)))")
        apply argo
       apply (simp add: last_tl)

     \<comment> \<open>MIN_BUDGET\<close>
       apply (rule schedule_used_MIN_BUDGET)
        apply clarsimp
        apply (case_tac "sc_refills sc", blast, case_tac list, fastforce
               , simp add: word_le_nat_alt refills_sum_def)
       apply clarsimp
       apply (case_tac "sc_refills sc")
        apply fast
       apply (case_tac list)
        apply force
       apply (rule_tac y="unat (sc_budget sc)" in order_trans)
        apply fastforce
       apply (simp add: word_le_nat_alt[symmetric])
      apply clarsimp
      apply (case_tac "na=0")
       apply clarsimp
      apply (drule_tac x="na + Suc 0" in spec)
      apply (elim impE)
       apply linarith
      apply (case_tac "sc_refills sc", force, case_tac list, force, force)

    \<comment> \<open>period_window\<close>
     apply (simp add: schedule_used.simps)
     apply (clarsimp simp: Let_def split: if_splits)
     apply (intro conjI impI)

          \<comment> \<open>list of length two, and first branch of schedule_used\<close>
          apply (frule order.strict_implies_order)
          apply (subgoal_tac "unat (r_time (refill_hd sc)) + unat (sc_period sc)
                              \<le> unat max_word")
           apply (frule_tac head_time="r_time (refill_hd sc)"
                        and period="sc_period sc"
                        and larger="MIN_BUDGET"
                        and smaller="usage"
                         in refill_word_proof_helper)
             using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
            apply fastforce
           apply (simp add: window_def)
           apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
            apply clarsimp
            apply (rule nat_move_sub_le)
            apply (simp add: ordered_disjoint_def)
            apply (drule_tac x=0 in spec)
            apply (elim impE)
            using tail_nonempty_length apply force
            apply (metis hd_conv_nth Nitpick.size_list_simp(2) nth_tl numeral_1_eq_Suc_0
                         zero_less_numeral)
           using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
         apply simp

       \<comment> \<open>list of length two, and second branch of schedule used\<close>
         apply (subst period_window_single)
          apply simp
         apply clarsimp
         apply (rule_tac y="unat (sc_budget sc)" in order_trans)
          apply (case_tac "sc_refills sc", fast, case_tac list, fastforce)
          apply (simp add: add_ac)
         apply (simp add: word_le_nat_alt)

      \<comment> \<open>list of length two, and last branch of schedule_used\<close>
        apply (simp add: window_def)
        apply (rule nat_move_sub_le)
        apply (simp add: ordered_disjoint_def)
        apply (drule_tac x=0 in spec)
        apply (elim impE)
         using tail_nonempty_length apply force
        apply (metis Nitpick.size_list_simp(2) hd_conv_nth nth_tl numeral_1_eq_Suc_0
                     zero_less_numeral)

       \<comment> \<open>list of length greater than two, and first branch of schedule_used\<close>
       apply (simp add: window_def)
       apply (frule order.strict_implies_order)
       apply (subgoal_tac "unat (r_time (refill_hd sc)) + unat (sc_period sc) \<le> unat max_word")
        apply (frule_tac head_time="r_time (refill_hd sc)"
                     and period="sc_period sc"
                     and larger="MIN_BUDGET"
                     and smaller="usage"
                      in refill_word_proof_helper)
          using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
         apply fastforce
        apply (simp add: window_def)
        apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
         apply clarsimp
         apply (rule nat_move_sub_le)
         apply (simp add: ordered_disjoint_def)
         apply (drule_tac x=0 in spec)
         apply (elim impE)
          using tail_nonempty_length apply force
         apply (metis hd_conv_nth length_greater_0_conv nth_tl)
        using word_le_nat_alt MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
       apply simp

     \<comment> \<open>list of length greater than two, and second branch of schedule_used\<close>
      apply (simp add: window_def)
      apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (tl (sc_refills sc)))))
                          = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                            - unat (r_amount (last (tl (tl (sc_refills sc)))))")
       apply (subgoal_tac "unat (r_amount (last (tl (tl (sc_refills sc)))) + usage)
                           = unat (r_amount (last (tl (tl (sc_refills sc))))) + unat usage")
        apply (subgoal_tac "unat (r_amount (last (tl (tl (sc_refills sc)))))
                            \<le> unat (sc_period sc)")
         apply clarsimp
         apply (rule nat_move_sub_le)
         apply (simp add: ordered_disjoint_def)
         apply (drule_tac x=0 in spec)
         apply (elim impE)
          using tail_nonempty_length apply force
         apply (metis hd_conv_nth list.exhaust_sel nth_Cons_Suc)
        apply (rule_tac y="unat (sc_budget sc)" in order_trans)
         apply (rule_tac t="unat (sc_budget sc)"
                     and s="sum_list (map unat (map r_amount (sc_refills sc)))"
                      in subst)
          apply clarsimp
         apply (rule member_le_sum_list)
         apply (simp add: last_tl)
        using word_le_nat_alt apply fast
       apply (rule unat_add_lem')
       apply (rule_tac y="unat (r_amount (last (tl (tl (sc_refills sc)))))
                          + unat (r_amount (refill_hd sc))"
                    in le_less_trans)
        apply clarsimp
       apply (rule_tac y="unat (sc_budget sc)" in le_less_trans)
        apply (simp add: add_ac)
        apply (case_tac "sc_refills sc", fast, case_tac list, force, clarsimp)
        apply (subgoal_tac "unat (r_amount (last lista))
                            \<le> sum_list (map unat (map r_amount lista))")
         apply linarith
        apply (rule member_le_sum_list)
        apply (simp add: last_tl)
       using max_word_def apply force
      apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (tl (sc_refills sc)))))
                          = unat (r_time (refill_hd sc) + sc_period sc)
                            - unat (r_amount (last (tl (tl (sc_refills sc)))))")
       apply clarsimp
      apply (subgoal_tac "r_amount (last (tl (tl (sc_refills sc))))
                          \<le> r_time (refill_hd sc) + sc_period sc")
       apply (simp add: unat_sub)
      apply (simp add: word_le_nat_alt)
      apply (rule_tac y="unat (sc_budget sc)" in order_trans)
       apply (erule_tac t="unat (sc_budget sc)"
                    and s="sum_list (map unat (map r_amount (sc_refills sc)))"
                     in subst)
       apply (rule member_le_sum_list, simp add: last_tl)
      apply linarith

     \<comment> \<open>list of length greater than two, and last branch of schedule_used\<close>
     apply (simp add: window_def)
     apply (rule nat_move_sub_le)
     apply (simp add: ordered_disjoint_def)
     apply (drule_tac x=0 in spec)
     apply (elim impE)
      apply (metis gt_or_eq_0 list.exhaust_sel list.size(4) list_exhaust_size_eq0 nat_simps(1))
     apply (metis hd_conv_nth list.exhaust_sel nth_Cons_Suc)

    \<comment> \<open>length\<close>
    apply (metis schedule_used_non_nil Nitpick.size_list_simp(2) not_numeral_le_zero
                 numeral_1_eq_Suc_0)
   apply (rule_tac y="Suc (length (\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                    r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>
                      # tl (tl (sc_refills sc))))"
                in order_trans)
    using schedule_used_length_max apply fast
   apply (subgoal_tac "length (\<lparr>r_time = r_time (hd (tl (sc_refills sc))) - (r_amount (refill_hd sc) - usage),
                                r_amount = r_amount (hd (tl (sc_refills sc))) + (r_amount (refill_hd sc) - usage)\<rparr>
                              # tl (tl (sc_refills sc)))
                       = length (sc_refills sc) - Suc 0")
    apply clarsimp
   apply (metis Nitpick.size_list_simp(2) append_len2 length_Cons length_append_singleton list.size(3))

  apply (clarsimp simp: unat_le_mono word_le_not_less[symmetric])
  apply (clarsimp simp: unat_le_mono[symmetric])
  apply (rule sc_valid_refills_amounts_bounded)
  apply (clarsimp simp: sc_valid_refills_def vs_all_heap_simps)
  apply simp
  apply (clarsimp simp: unat_le_mono[symmetric])

  \<comment> \<open>last branch of refill_budget_check - remnant is at least MIN_BUDGET.
      We leave the remnant in place, and do schedule_used of usage\<close>
  apply (clarsimp simp: vs_all_heap_simps sc_valid_refills_def obj_at_def set_object_def
                        get_object_def
                 split: if_splits)

  \<comment> \<open>we introduce some useful facts\<close>
  apply (frule sc_refill_ready_release_time_well_bounded, clarsimp, clarsimp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps)
   apply (clarsimp simp: valid_refills_def vs_all_heap_simps)
  apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD")
   apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
    apply (subgoal_tac "unat usage \<le> unat (r_amount (refill_hd sc))")
  apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
         ; (simp add: refills_sum_def)?)
    using MIN_BUDGET_pos word_le_nat_alt unat_gt_0 apply fastforce
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force
  apply (subgoal_tac "unat (r_time (refill_hd sc) + usage)
                      = unat (r_time (refill_hd sc)) + unat usage")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)
  apply (subgoal_tac "unat (r_amount (refill_hd sc) - usage)
                      = unat (r_amount (refill_hd sc)) - unat usage")
   prefer 2
   using unat_sub word_not_le apply blast
  apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                      = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)
  apply (subgoal_tac "unat (r_amount (refill_hd sc)) \<le> unat (sc_period sc)")
   prefer 2
   apply (rule_tac y="unat (sc_budget sc)" in order_trans)
    apply (erule_tac s="sum_list (map unat (map r_amount (sc_refills sc)))"
                 and t="unat (sc_budget sc)"
                  in subst)
    apply (rule_tac member_le_sum_list)
    apply force
   apply (simp add: word_le_nat_alt)
  apply (frule_tac y=usage and x="r_amount (refill_hd sc)" in leI)
  \<comment> \<open>end of the proof of useful facts\<close>

  apply (intro conjI)

       \<comment> \<open>refills_sum\<close>
        apply (case_tac "sc_refills sc", simp, simp)

       \<comment> \<open>ordered_disjoint\<close>
       apply (rule schedule_used_ordered_disjoint)
         apply (rule_tac left="[\<lparr>r_time = r_time (refill_hd sc) + usage,
                                 r_amount = r_amount (refill_hd sc) - usage\<rparr>]"
                     and right="tl (sc_refills sc)"
                      in ordered_disjoint_append)
            apply (simp add: ordered_disjoint_def)
           apply (simp add: ordered_disjoint_sublist)
          apply (clarsimp simp: unat_sub word_le_nat_alt ordered_disjoint_def)
          apply (drule_tac x=0 in spec)
          apply (elim impE)
           apply (metis Nitpick.size_list_simp(2) gt_or_eq_0 length_0_conv nat_simps(2)
                        semiring_norm(164) semiring_norm(50))
          apply (simp add: hd_conv_nth)
          apply (subgoal_tac "tl (sc_refills sc) ! 0 = sc_refills sc ! Suc 0", simp)
          apply (meson length_greater_0_conv nth_tl)
         apply force
        apply clarsimp
        apply (case_tac "m=0")
         apply clarsimp
         apply force
        apply clarsimp
        apply (drule_tac x=m in spec)
        apply clarsimp
        apply (case_tac "sc_refills sc", fast, case_tac list, simp, force)
       apply (clarsimp split: if_splits)
        apply (simp add: unat_sub word_le_nat_alt)
      apply (simp add: window_def)
       apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))")
        apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc)
                            = unat (r_time (refill_hd sc)) + unat (sc_period sc)")
         apply clarsimp
        apply (rule unat_add_lem', simp add: max_word_def)
       apply (simp add: last_tl)

      \<comment> \<open>no_overflow\<close>
      apply (rule schedule_used_no_overflow)
         apply (rule_tac left="[\<lparr>r_time = r_time (refill_hd sc) + usage,
                                 r_amount = r_amount (refill_hd sc) - usage\<rparr>]"
                     and right="tl (sc_refills sc)"
                      in no_overflow_append)
           apply (simp add: no_overflow_def word_le_nat_alt)
          apply (drule_tac x=0 in spec)
          apply (metis hd_Cons_tl no_overflow_tail)
         apply fastforce
        apply (simp add: no_overflow_def)
       apply clarsimp
       apply (case_tac "m=0")
        apply simp
       apply clarsimp
       apply (drule_tac x=m in spec)
       apply (elim impE)
        apply blast
       apply (subgoal_tac "tl (sc_refills sc) ! (m - Suc 0) = sc_refills sc ! m")
        prefer 2
        apply (metis Nitpick.size_list_simp(2) length_ineq_not_Nil(1) less_handy_casesE
                     less_le_nonzero_helper minus_eq nat_Suc_less_le_imp nat_simps(2) nth_tl
                     semiring_norm(164))
       apply argo
      apply (clarsimp split: if_splits)
       apply (simp add: word_le_nat_alt)
      apply (simp add: window_def)
      apply (subgoal_tac "refill_tl sc = last (tl (sc_refills sc))", simp, simp add: last_tl)

     \<comment> \<open>MIN_BUDGET\<close>
     apply (subgoal_tac "sum_list (map unat (map r_amount ((\<lparr>r_time = r_time (refill_hd sc) + usage,
                                                             r_amount = r_amount (refill_hd sc) - usage\<rparr>
                                                           # tl (sc_refills sc))
                                                           @ [\<lparr>r_time = r_time (refill_hd sc) + sc_period sc,
                                                               r_amount = usage\<rparr>])))
                         = unat (sc_budget sc)")
      prefer 2
      apply (case_tac "sc_refills sc")
       apply blast
      apply (case_tac list)
       apply (simp add: word_le_nat_alt refills_sum_def)
      apply (simp add: le_def unat_sub unat_arith_simps(2))
     apply (rule schedule_used_MIN_BUDGET)
       using word_le_nat_alt apply metis
      apply clarsimp
      using word_le_nat_alt apply fast
     apply clarsimp
     apply (case_tac "na=0")
      apply force
     apply (drule_tac x=na in spec)
     apply clarsimp
     apply (case_tac "sc_refills sc", fast, case_tac list, simp, force)

    \<comment> \<open>period window\<close>
    \<comment> \<open>first branch of schedule_used\<close>
    apply (case_tac "usage < MIN_BUDGET \<and> \<not>(length (sc_refills sc) = sc_refill_max sc)
                     \<and> 2 * MIN_BUDGET \<le> r_amount (last (tl (sc_refills sc))) + usage")

     \<comment> \<open>we introduce a useful fact\<close>
     apply (subgoal_tac "unat (r_time (refill_hd sc)) + unat (sc_period sc)
                         \<le> unat max_time")
      prefer 2
     apply simp
     apply (frule_tac head_time="r_time (refill_hd sc)"
                  and period="sc_period sc"
                  and larger="MIN_BUDGET"
                  and smaller="usage"
                   in refill_word_proof_helper)
       using MIN_BUDGET_le_MIN_SC_BUDGET apply force
      apply fastforce
     \<comment> \<open>end of the proof of the useful fact\<close>

     apply (clarsimp simp: schedule_used.simps Let_def split: if_splits)
     apply (intro conjI impI)

       \<comment> \<open>first of three branches (for the first branch of schedule_used)\<close>
       apply (simp add: window_def)
       apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
        using word_le_nat_alt apply force
       using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce

      \<comment> \<open>second of the three  branches ((for the first branch of schedule_used)\<close>
      apply (subst period_window_single)
       apply simp
      apply clarsimp

     \<comment> \<open>last of the three branches (for the first branch of schedule_used)\<close>
     apply (simp add: window_def)
     apply (subgoal_tac "MIN_BUDGET \<le> sc_period sc")
      using word_le_nat_alt apply force
     using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce

    \<comment> \<open>second branch of schedule_used\<close>
    apply (case_tac "usage< MIN_BUDGET \<or> (length (sc_refills sc) = sc_refill_max sc)")
     apply (clarsimp simp: schedule_used.simps Let_def split: if_splits)
     apply (intro conjI impI; (simp add: window_def)?)

        \<comment> \<open>first of two branches (for the second branch of schedule_used)\<close>
        apply clarsimp
        apply (subgoal_tac "unat (r_time (refill_hd sc)) + unat (sc_period sc)
                            \<le> unat max_time")
        apply (frule_tac head_time="r_time (refill_hd sc)"
                     and period="sc_period sc"
                     and larger="MIN_BUDGET"
                     and smaller="usage"
                      in refill_word_proof_helper)
          using MIN_BUDGET_le_MIN_SC_BUDGET apply force
         apply fastforce
        apply (simp add: window_def)
        apply (subgoal_tac "unat MIN_BUDGET \<le> unat (sc_period sc)")
         apply linarith
        using MIN_BUDGET_le_MIN_SC_BUDGET word_le_nat_alt apply fastforce
       apply simp

     \<comment> \<open>last of the two branches (for the second branch of schedule_used)\<close>
     \<comment> \<open>a useful fact\<close>
     apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc)))) \<le> unat (sc_period sc)")
      prefer 2
      apply (rule_tac y="unat (sc_budget sc)" in order_trans)
       apply (erule_tac s="sum_list (map unat (map r_amount (sc_refills sc)))"
                    and t="unat (sc_budget sc)"
                     in subst)
       apply (rule member_le_sum_list)
       apply (simp add: last_tl)
      apply (simp add: word_le_nat_alt)
     \<comment> \<open>end of the proof of the useful fact\<close>

     apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (sc_refills sc))))
                         = unat (r_time (refill_hd sc)) + unat (sc_period sc)
                           - unat (r_amount (last (tl (sc_refills sc))))")
      apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc))) + usage)
                          = unat (r_amount (last (tl (sc_refills sc)))) + unat usage")
       apply (subgoal_tac "unat (r_amount (last (tl (sc_refills sc)))) \<le> unat (sc_period sc)")
        apply clarsimp
       apply blast
      apply (rule unat_add_lem', simp add: max_word_def)
     apply (subgoal_tac "unat (r_time (refill_hd sc) + sc_period sc - r_amount (last (tl (sc_refills sc))))
                         = unat (r_time (refill_hd sc) + sc_period sc)
                           - unat (r_amount (last (tl (sc_refills sc))))")
      apply clarsimp
     apply (subgoal_tac "r_amount (last (tl (sc_refills sc)))
                         \<le> r_time (refill_hd sc) + sc_period sc")
      apply (simp add: unat_sub)
     apply (simp add: word_le_nat_alt)

    \<comment> \<open>last branch of schedule_used\<close>
    apply (simp add: window_def schedule_used.simps)

   \<comment> \<open>length\<close>
   apply (metis schedule_used_non_nil Nitpick.size_list_simp(2) not_numeral_le_zero
                numeral_1_eq_Suc_0)
   apply (case_tac "length (sc_refills sc) < sc_refill_max sc")
   apply (subgoal_tac "length (\<lparr>r_time = r_time (refill_hd sc) + usage,
                                r_amount = r_amount (refill_hd sc) - usage\<rparr>
                               # tl (sc_refills sc))
                       = length (sc_refills sc)")
    apply (metis (no_types, hide_lams) schedule_used_length_max le_def le_trans nat_Suc_less_le_imp)
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "length (\<lparr>r_time = r_time (refill_hd sc) + usage,
                               r_amount = r_amount (refill_hd sc) - usage\<rparr>
                              # tl (sc_refills sc))
                      = length (sc_refills sc)")
   using schedule_used_length_full apply force
  apply clarsimp
  apply (metis diff_Suc_Suc list_exhaust_size_eq0 minus_nat.diff_0 old.nat.exhaust)

  apply (clarsimp simp: unat_le_mono word_le_not_less[symmetric])
  apply (clarsimp simp: unat_le_mono[symmetric])
  apply (rule sc_valid_refills_amounts_bounded)
  apply (clarsimp simp: sc_valid_refills_def vs_all_heap_simps)
  apply simp
  apply (clarsimp simp: unat_le_mono[symmetric])
  done

lemma valid_refills_sc_update:
  "(valid_refills p (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>))
       = sc_valid_refills sc"
  by (clarsimp simp: obj_at_def vs_all_heap_simps)

lemma update_sc_consumed_valid_refills[wp]:
  "\<lbrace>valid_refills p and sc_at ptr\<rbrace>
   update_sched_context ptr (\<lambda>sc. sc_consumed_update f sc)
      \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  by (wpsimp simp: obj_at_def vs_all_heap_simps window_def
                      update_sched_context_def obj_at_def
                  wp: set_object_wp get_object_wp )

lemma valid_refills_sc_consumed_update[iff]:
    "valid_refills p (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext (sc\<lparr>sc_consumed:=x\<rparr>) n)\<rparr>)
         = valid_refills p (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext sc n)\<rparr>)"
  by (clarsimp simp: obj_at_def vs_all_heap_simps window_def)

lemma valid_refills_domain_time_update[simp]:
  "valid_refills sc (domain_time_update f s) = valid_refills sc s"
  by (simp add: obj_at_def vs_all_heap_simps)

lemma MIN_BUDGET_lower_bounds[elim!]:
  "MIN_SC_BUDGET \<le> k \<Longrightarrow> MIN_BUDGET \<le> k"
  by (erule order_trans[OF MIN_BUDGET_le_MIN_SC_BUDGET])

lemma refill_budget_check_round_robin_valid_refills[wp]:
   "\<lbrace>valid_refills p
     and current_time_bounded 1
     and K (unat usage + unat MAX_SC_PERIOD \<le> unat max_time)\<rbrace>
    refill_budget_check_round_robin usage
    \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: refill_budget_check_round_robin_def is_round_robin_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])

  apply (subst hoare_pre_add[where R="\<lambda>s.
                 unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time"])
    apply (clarsimp simp: current_time_bounded_def)

  apply (rule hoare_if)
   apply (rule hoare_if)
    apply (wpsimp wp: set_refills_wp)

    apply (prop_tac "\<exists>hr. sc_refills sc = [hr]")
     apply (case_tac "sc_refills sc"; simp)

    apply (clarsimp simp: vs_all_heap_simps valid_refills_def obj_at_def MIN_REFILLS_def split: if_splits)

     apply (prop_tac "unat (cur_time s) + unat (sc_budget sc - MIN_BUDGET) \<le> unat max_word")
      apply (erule_tac order_trans[rotated], overflow_hammer)
      apply (rule iffD1[OF word_le_nat_alt])
      apply (erule order_trans[rotated])
      apply (rule word_sub_le)
      apply blast
     apply (prop_tac "unat (cur_time s) + unat (sc_budget sc) \<le> unat max_word")
      apply (erule add_left_mono_trans, overflow_hammer)
     apply (prop_tac "unat MIN_BUDGET \<le> unat (cur_time s) + unat (sc_budget sc)")
      apply (rule order.trans, overflow_hammer, simp)

     apply (intro conjI allI impI)
       \<comment> \<open>ordered_disjoint\<close>
        apply (clarsimp simp: ordered_disjoint_def)
        apply (rule eq_imp_le)
        apply (subst unat_add_lem'_sym, overflow_hammer)
        apply clarsimp
        \<comment> \<open>no_overflow\<close>
       apply (clarsimp simp: no_overflow_def)
       apply (case_tac n; simp)
       apply (subst unat_sub)
        apply (erule order.trans, overflow_hammer)
       apply (subst le_add_diff_inverse2)
        apply (subst unat_add_lem'; overflow_hammer)
       apply (subst unat_add_lem'; overflow_hammer)
     \<comment> \<open>bounded below\<close>
      apply (case_tac n; simp)
      apply (rule word_l_diffs(4); simp)
      apply (metis MIN_BUDGET_le_MIN_SC_BUDGET MIN_REFILLS_def MIN_SC_BUDGET_def)
        \<comment> \<open>window\<close>
     apply (clarsimp simp: window_def)
     apply (subst unat_sub)
      apply (rule order_trans[OF MIN_BUDGET_le_MIN_SC_BUDGET])
      apply (erule order_trans)
      apply (subst olen_add_eqv[symmetric])
      apply (subst no_olen_add_nat)
      apply (rule order.strict_trans1[OF add_left_mono])
       apply (erule iffD1[OF word_le_nat_alt])
      apply (erule order.strict_trans1)
      apply (clarsimp simp: max_word_def)
     apply (subst le_add_diff_inverse2)
      apply (subst unat_add_lem', overflow_hammer)
      apply (rule order.trans[OF _ le_add2])
      apply (erule iffD1[OF word_le_nat_alt])
     apply (subst unat_add_lem', overflow_hammer, simp)

    apply (prop_tac "unat MIN_BUDGET \<le> unat MAX_SC_PERIOD")
     apply (rule_tac y="unat (sc_budget sc)" in order_trans; overflow_hammer)
    apply (prop_tac "usage \<le> sc_budget sc")
     apply (erule_tac y="usage + MIN_BUDGET" in order_trans[rotated])
     apply (overflow_hammer)
     apply (erule (1) add_left_mono_trans)
    apply (prop_tac " unat (cur_time s) + unat (sc_budget sc) \<le> unat max_word")
     apply (erule add_left_mono_trans, overflow_hammer)
    apply (prop_tac "unat (cur_time s) + unat (sc_budget sc - usage) \<le> unat max_word")
     apply (rule_tac y="unat (sc_budget sc)" in add_left_mono_trans, overflow_hammer)
     apply (rule iffD1[OF word_le_nat_alt])
     apply (overflow_hammer)
    apply (prop_tac "usage \<le> (cur_time s + sc_budget sc)")
     apply (erule order_trans, overflow_hammer)

    apply (intro conjI allI impI)
         \<comment> \<open>ordered_disjoint\<close>
       apply (clarsimp simp: ordered_disjoint_def)
       apply (subst add_diff_eq[symmetric])
       apply (subst unat_add_lem'_sym; overflow_hammer)
      \<comment> \<open>no_overflow\<close>
      apply (clarsimp simp: no_overflow_def)
      apply (case_tac n; simp)
      apply (subst unat_sub)
       apply (erule_tac y="sc_budget sc" in order_trans)
       apply overflow_hammer
      apply (subst add_diff_assoc2, overflow_hammer)
      apply simp
      apply (subst unat_add_lem'; overflow_hammer)
     \<comment> \<open>bounded below\<close>
     apply (case_tac n; simp)
     apply (erule le_minus', overflow_hammer)
     apply (erule add_left_mono_trans)
     apply (subst word_le_nat_alt[symmetric], fastforce)
    \<comment> \<open>window\<close>
    apply (clarsimp simp: window_def)
    apply (subst unat_sub, overflow_hammer)
    apply (subst add_diff_assoc2, overflow_hammer)
    apply simp
    apply (subst unat_add_lem'; overflow_hammer)

   apply (wpsimp wp: set_refills_wp)

   apply (prop_tac "\<exists>h t. sc_refills sc = [h, t]")
    apply (case_tac "sc_refills sc"; simp)
    apply (case_tac "list"; simp)
   apply (clarsimp simp: vs_all_heap_simps valid_refills_def obj_at_def MIN_REFILLS_def split: if_splits)
   apply (prop_tac "unat (r_amount h) + unat (r_amount t) \<le> unat max_time")
    apply (rule_tac y="unat (r_time h) + unat (r_amount h) + unat (r_amount t)" in order_trans, simp)
    apply (rule_tac y="unat (r_time t) + unat (r_amount t)" in order_trans, simp)
     apply (clarsimp simp: ordered_disjoint_def)
    apply (clarsimp simp: no_overflow_def)
    apply (drule_tac x=1 in spec)+
    apply simp
   apply (prop_tac "unat (r_amount h) \<le> unat MAX_SC_PERIOD")
    apply (rule_tac y="unat (r_amount h + r_amount t)" in order_trans)
     apply (subst unat_add_lem', overflow_hammer)
     apply simp
    apply (simp, overflow_hammer)
   apply (prop_tac "unat (r_amount t) \<le> unat MAX_SC_PERIOD")
    apply (rule_tac y="unat (r_amount h + r_amount t)" in order_trans)
     apply (subst unat_add_lem', overflow_hammer)
     apply simp
    apply (simp, overflow_hammer)
   apply (prop_tac "usage \<le> r_amount h")
    apply (erule_tac order_trans[rotated], overflow_hammer)
    apply (erule add_left_mono_trans)
    apply (erule_tac order_trans[rotated])
    apply (rule iffD1[OF word_le_nat_alt], fastforce)
   apply (prop_tac "unat (r_amount h - usage) \<le> unat MAX_SC_PERIOD")
    apply (erule_tac y="unat (r_amount h)" in order_trans[rotated])
    apply (rule iffD1[OF word_le_nat_alt], overflow_hammer)
   apply (prop_tac "unat MIN_BUDGET \<le> unat MAX_SC_PERIOD")
    apply (rule_tac y="unat (sc_budget sc)" in order_trans[rotated])
     apply (rule iffD1[OF word_le_nat_alt], overflow_hammer)
    apply (rule iffD1[OF word_le_nat_alt], fastforce)

   apply (intro conjI allI impI)
       \<comment> \<open>ordered_disjoint\<close>
      apply (clarsimp simp: ordered_disjoint_def)
      apply (subst add_diff_eq[symmetric])
      apply (subst unat_add_lem'_sym; overflow_hammer)
      apply (erule add_left_mono_trans, overflow_hammer)
    \<comment> \<open>no overflow\<close>
     apply (clarsimp simp: no_overflow_def)
     apply (case_tac na; simp)
     apply (subst unat_add_lem', overflow_hammer)
      apply (subst add.commute)
      apply (erule add_left_mono_trans, overflow_hammer)
     apply (subst unat_sub)
      apply (erule order_trans, overflow_hammer)
      apply (erule add_left_mono_trans, overflow_hammer)
     apply (subst add_diff_assoc2)
      apply (rule_tac y="unat (r_amount h)" in order_trans, overflow_hammer)
      apply (subst unat_add_lem', overflow_hammer)
       apply (erule add_left_mono_trans, overflow_hammer)
      apply simp
     apply (simp)
     apply (subst unat_add_lem', overflow_hammer)
      apply (erule add_left_mono_trans, overflow_hammer)
     apply (subst add.assoc)
     apply (erule add_left_mono_trans)
     apply (subst unat_add_lem'_sym, overflow_hammer)
     apply (rule_tac y="unat (sc_budget sc)" in order_trans)
      apply (rule iffD1[OF word_le_nat_alt], simp)
     apply overflow_hammer
    apply (case_tac na; simp)
     apply (erule le_minus', overflow_hammer)
     apply (erule add_left_mono_trans, overflow_hammer)
    apply (rule_tac y="r_amount t" in  order_trans)
     apply fastforce
    apply overflow_hammer
    apply (subst add.commute)
    apply (erule add_left_mono_trans, simp)
    \<comment> \<open>window\<close>
   apply (clarsimp simp: window_def)
   apply (subst unat_add_lem', overflow_hammer)
    apply (subst add.commute)
    apply (erule add_left_mono_trans, simp)
   apply (subst add_diff_eq[symmetric])
   apply (subst unat_add_lem', overflow_hammer)
    apply (rule order.trans)
     apply (rule add_left_mono)
     apply (subst word_le_nat_alt[symmetric])
     apply (rule word_sub_le, assumption)
    apply (erule add_left_mono_trans, simp)
   apply (clarsimp)
   apply (subst unat_sub, simp)
   apply (subst add_diff_assoc2, overflow_hammer)
   apply clarsimp
   apply (subst unat_add_lem'[symmetric], overflow_hammer)
   apply (rule iffD1[OF word_le_nat_alt], simp)
  apply clarsimp

  apply (wpsimp wp: set_refills_wp)
  apply (clarsimp simp: vs_all_heap_simps valid_refills_def obj_at_def MIN_REFILLS_def
                        ordered_disjoint_def no_overflow_def window_def
                 split: if_splits)
   apply (intro conjI)
    apply (erule order_trans[OF add_left_mono, rotated])
    apply (rule order_trans)
     apply (erule iffD1[OF word_le_nat_alt], simp)
  using MIN_BUDGET_lower_bounds apply blast
  apply (intro conjI)
   apply (erule order_trans[OF add_left_mono, rotated])
   apply (rule order_trans)
    apply (erule iffD1[OF word_le_nat_alt], simp)
  using MIN_BUDGET_lower_bounds apply blast
  done

lemma consumed_time_bounded_helper:
  "consumed_time_bounded s
   \<Longrightarrow> current_time_bounded 1 s
   \<Longrightarrow> unat (consumed_time s) + unat MAX_SC_PERIOD \<le> unat max_time"
  unfolding consumed_time_bounded_def current_time_bounded_def
  by linarith

lemmas valid_refills_kheap_tcb_update'[iff] = valid_refills_kheap_tcb_update[simplified fun_upd_def obj_at_def is_tcb]

(* FIXME: move *)
lemma sc_at_tcb_update[iff]:
  "tcb_at epptr s \<Longrightarrow>
   scs_of_kh (kheap s(epptr \<mapsto> TCB ko)) = scs_of s"
  by (rule map_eqI, auto simp add: vs_heap_simps obj_at_def is_tcb)

lemma thread_set_valid_sched_misc[wp]:
  "thread_set f t \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (sc_refill_cfgs_of s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (subst sc_at_tcb_update; clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps is_tcb)
  done

lemma reply_push_valid_sched_misc[wp]:
  "reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (last_machine_time_of s) (etcbs_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)
          (ep_send_qs_of s) (ep_recv_qs_of s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp hoare_vcg_if_lift2 hoare_drop_imps hoare_vcg_all_lift
           simp: reply_push_def)

crunch valid_refills[wp]: set_cdt,set_original,set_extra_badge "valid_refills scp"
  (wp_del: set_original_wp)

crunch valid_sched_pred_strong[wp]: set_extra_badge "valid_sched_pred_strong P"

lemma transfer_caps_valid_sched_pred_strong[wp]:
  "transfer_caps info caps ep recv recv_buf \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

lemma transfer_caps_loop_valid_refills[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_refills scp\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_refills scp\<rbrace>"
  by (wp transfer_caps_loop_pres)

context DetSchedSchedule_AI begin

crunches copy_mrs, make_fault_msg, do_ipc_transfer
  for sc_refill_cfgs_of[wp]: "(\<lambda>s. P (sc_refill_cfgs_of s)) :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_wp')

crunches send_ipc
  for valid_sched_misc[wp]:
    "\<lambda>s :: 'state_ext state. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s)
                               (cur_thread s) (idle_thread s) (last_machine_time_of s)
                               (etcbs_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)"
  (wp: crunch_wps)

crunch valid_refills[wp]: handle_timeout "valid_refills scp :: 'state_ext state \<Rightarrow> bool"

lemma end_timeslice_valid_refills[wp]:
  "end_timeslice canTimeout \<lbrace>valid_refills scptr :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  supply if_weak_cong[cong del]
  apply (clarsimp simp: end_timeslice_def)
  by (wpsimp simp: end_timeslice_def wp: hoare_drop_imps split_del: if_split)

end

(* FIXME: merge is_active_sc with existing notion *)
lemma active_implies_valid_refills:
  "is_active_sc scp s \<Longrightarrow> active_sc_valid_refills s \<Longrightarrow> valid_refills scp s"
  unfolding active_sc_valid_refills_def
  by (clarsimp simp: vs_all_heap_simps )

lemma active_implies_valid_refills_tcb_at:
  "active_sc_tcb_at t s
   \<Longrightarrow> active_sc_valid_refills s
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp \<and> valid_refills scp s) t s"
  apply (prop_tac "bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp) t s", clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps is_tcb)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (erule active_implies_valid_refills[rotated])
  apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps  active_sc_def)
  done

lemma active_sc_tcb_at_def2:
  "active_sc_tcb_at t s = ((\<exists>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<and> is_sc_active scp s))"
  by (intro iffI;
      fastforce simp: vs_all_heap_simps tcb_at_kh_simps is_sc_active_def
               split: option.splits kernel_object.splits)

lemma active_sc_tcb_at_bound_valid_refills:
  "active_sc_tcb_at t s
   \<Longrightarrow> active_sc_valid_refills s
   \<Longrightarrow> (\<forall>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<longrightarrow> valid_refills scp s)"
  apply (drule (1) active_implies_valid_refills_tcb_at)
  apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)
  done

(* FIXME: move *)
lemma set_takeWhileD_contrap:
  "a \<notin> set xs \<Longrightarrow> a \<notin> set (takeWhile P xs)"
  by (fastforce dest: set_takeWhileD)

lemma valid_refills_refill_sufficient:
  "valid_refills scp s \<Longrightarrow> is_refill_sufficient 0 scp s"
  apply (clarsimp simp: valid_refills_def sc_valid_refills_def vs_all_heap_simps obj_at_def
                        refill_sufficient_defs)
  apply (rename_tac sc n)
  apply (case_tac "sc_refills sc"; simp)
  by fastforce

lemma budget_sufficient_def2:
  "budget_sufficient t s = ((\<exists>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<and> is_refill_sufficient 0 scp (s)))"
  by (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)

lemma active_sc_tcb_at_budget_sufficient:
  "active_sc_tcb_at t s \<Longrightarrow> active_sc_valid_refills s \<Longrightarrow> budget_sufficient t (s :: 'z :: state_ext state)"
  by (fastforce simp: budget_sufficient_def2 active_sc_tcb_at_def2 is_sc_active_kh_simp
                dest: valid_refills_refill_sufficient active_implies_valid_refills)

lemma awaken_valid_sched:
  "\<lbrace>valid_sched
    and valid_idle
    and (\<lambda>s. cur_thread s \<in> set (release_queue s) \<longrightarrow> \<not> budget_ready (cur_thread s) s)\<rbrace>
   awaken
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding awaken_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_valid_sched_helper simp: valid_sched_def)
  apply (simp only: dropWhile_eq_drop[symmetric])
  apply (strengthen distinct_takeWhile valid_release_q_2_dropWhile)
  apply (intro conjI)
         apply (clarsimp)
        apply (clarsimp simp: ready_or_release_2_def in_queue_2_def in_ready_q_def
                       dest!: set_dropWhileD
               , blast)
       apply (erule valid_sched_action_2_subset_eq[rotated], clarsimp dest!: set_dropWhileD)
      apply (clarsimp)
     apply (rule set_takeWhileD_contrap)
     apply (clarsimp simp: not_in_release_q_def valid_release_q_def)
     apply (drule_tac x="idle_thread s" in bspec, simp, clarsimp)
     apply (drule st_tcb_at_idle_thread[simplified tcb_at_kh_simps], simp, simp)
    apply (rule valid_blocked_dropWhile_rlq; clarsimp)
   apply (clarsimp dest!: set_takeWhileD)
   apply (frule valid_release_q_active_sc, simp)
   apply (clarsimp simp: fun_of_m_get_tcb_refill_ready opt_map_def map_project_def pred_map_simps)
  apply (intro allI ballI)
  apply (clarsimp simp: valid_release_q_def)
  apply (drule_tac x=target in bspec)
   apply (clarsimp dest!: set_takeWhileD)
  apply (intro conjI)
      apply (clarsimp simp: tcb_at_kh_simps)
     apply simp
    apply (clarsimp simp: not_in_release_q_def in_queue_2_def)
    apply (fastforce dest: dropWhile_takeWhile_distinct)
   apply (clarsimp dest!: set_takeWhileD)
   apply (subst (asm) fun_of_m_get_tcb_refill_budget_ready; clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)
  apply (clarsimp elim!: active_sc_tcb_at_budget_sufficient)
  done

crunches awaken
for cur_tcb[wp]: cur_tcb
and budget_ready: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient: "\<lambda>s. P (budget_sufficient t s)"
and budget_ready_ct: "\<lambda>s. P (budget_ready (cur_thread s) s)"
and budget_sufficient_ct: "\<lambda>s. P (budget_sufficient (cur_thread s) s)"
and active_sc_tcb_at'[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
and active_sc_tcb_at_ct[wp]: "\<lambda>s. P (active_sc_tcb_at(cur_thread s) s)"
  (wp: hoare_drop_imps mapM_x_wp')

(* commit_time *)

lemma sc_consumed_update_sc_tcb_sc_at[wp]:
  "update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := f (sc_consumed sc)\<rparr>)
   \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

crunches commit_domain_time, refill_budget_check, refill_budget_check_round_robin,
         refill_unblock_check
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain"
  and in_cur_domain[wp]: "in_cur_domain t"
  and valid_idle_etcb[wp]: "valid_idle_etcb"
  and etcb_at[wp]: "etcb_at P t"
  (wp: crunch_wps set_refills_budget_ready simp: crunch_simps)

lemma commit_time_sc_tcb_sc_at[wp]:
  "commit_time \<lbrace>\<lambda>s. sc_tcb_sc_at P sc_ptr s\<rbrace>"
   unfolding commit_time_def
   by (wpsimp wp: hoare_drop_imps)

crunches commit_time
  for simple_sched_action[wp]: "simple_sched_action"
  and ct_not_in_q[wp]: "ct_not_in_q"
  (wp: crunch_wps simp: crunch_simps)

lemma refill_budget_check_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_valid_sched_action_act_not is_round_robin_wp)

lemma refill_budget_check_round_robin_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check_round_robin usage
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: set_refills_valid_sched_action_act_not is_round_robin_wp)

lemma refill_budget_check_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_valid_ready_qs is_round_robin_wp
      split_del: if_split)

lemma refill_budget_check_round_robin_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)\<rbrace>
   refill_budget_check_round_robin usage
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: set_refills_valid_ready_qs is_round_robin_wp)

(* FIXME: Move *)
lemma precondition_cases:
  "\<lbrace>P and Q\<rbrace> f \<lbrace> R \<rbrace> \<Longrightarrow> \<lbrace>(\<lambda>s. \<not>P s) and Q\<rbrace> f \<lbrace> R \<rbrace> \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace> R \<rbrace>"
  apply (rule_tac Q="\<lambda>s. (P and Q) s \<or> ((\<lambda>s. \<not> P s) and Q) s" in hoare_weaken_pre)
  apply (rule_tac Q="\<lambda>rv s. R rv s \<or> R rv s" in hoare_strengthen_post)
  apply (rule hoare_vcg_disj_lift)
  by force+

lemma refill_budget_check_valid_release_q:
  "\<lbrace>valid_release_q and (\<lambda>s. sc_not_in_release_q (cur_sc s) s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding refill_budget_check_def
  supply if_split [split del]
  by (wpsimp wp: set_refills_valid_release_q is_round_robin_wp)

lemma refill_budget_check_round_robin_valid_release_q:
  "\<lbrace>valid_release_q and (\<lambda>s. sc_not_in_release_q (cur_sc s) s)\<rbrace>
   refill_budget_check_round_robin usage
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: set_refills_valid_release_q is_round_robin_wp)

lemma valid_state_sym_refs[dest]: "valid_state s \<Longrightarrow> sym_refs (state_refs_of s)"
  by (clarsimp simp: valid_state_def valid_pspace_def)

lemma refill_budget_check_round_robin_valid_sched_misc[wp]:
  "refill_budget_check_round_robin consumed
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s) (ready_queues s)
          (release_queue s) (scheduler_action s) (last_machine_time_of s) (etcbs_of s)
          (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: hoare_drop_imp)

lemma refill_budget_check_valid_sched_misc[wp]:
  "refill_budget_check consumed
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (sc_tcbs_of s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)
          (ep_send_qs_of s) (ep_recv_qs_of s)\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: hoare_drop_imp)

lemma commit_time_valid_sched_misc[wp]:
  "commit_time
   \<lbrace>\<lambda>s. P (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)
          (ep_send_qs_of s) (ep_recv_qs_of s)\<rbrace>"
  unfolding commit_time_def
  by (wpsimp wp: hoare_drop_imp)

lemma commit_time_valid_release_q:
  "\<lbrace>valid_release_q and cur_sc_in_release_q_imp_zero_consumed and valid_state\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding commit_time_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule_tac P="\<lambda>s. \<exists>tp. bound_sc_tcb_at ((=) (Some (cur_sc s))) tp s" in precondition_cases)
   apply (rule_tac P="\<lambda>s. sc_with_tcb_prop (cur_sc s) (\<lambda>s. in_release_q s) s" in precondition_cases)
    apply (rule_tac Q="valid_release_q and (\<lambda>s. consumed_time s = consumed)
                       and K (consumed = 0)"
                    in hoare_weaken_pre[rotated])
     apply (fastforce simp: vs_all_heap_simps obj_at_kh_kheap_simps)
    apply (rule hoare_gen_asm)
    apply clarsimp
    apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
    apply (clarsimp simp: vs_all_heap_simps valid_release_q_def obj_at_def)
   apply (rule_tac Q="valid_release_q and (\<lambda>s. \<exists>tp. bound_sc_tcb_at ((=) (Some (cur_sc s))) tp s)
                      and (\<lambda>s. sc_not_in_release_q (cur_sc s) s) and (\<lambda>s. cur_sc s = csc)"
                   in hoare_weaken_pre[rotated])
    apply (clarsimp, rule conjI, fastforce)
    apply (clarsimp simp: obj_at_def)
    apply (subgoal_tac "t = ta", clarsimp)
    apply (rule_tac z="cur_sc s" in sym_refs_bound_sc_tcb_at_inj)
      apply (clarsimp simp: valid_state_def valid_pspace_def, assumption)
     apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric] tcb_at_kh_simps pred_map_eq_def)
    apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric] tcb_at_kh_simps pred_map_eq_def)
  by (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imps
                 set_refills_valid_release_q
                 refill_budget_check_valid_release_q
           simp: refill_budget_check_round_robin_def | rule conjI)+

lemma commit_time_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
   unfolding commit_time_def
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imp
                     set_refills_valid_ready_qs refill_budget_check_valid_ready_qs_not_queued
                     refill_budget_check_round_robin_valid_ready_qs_not_queued
               simp:  split_del: if_split)
   apply (clarsimp simp: cur_sc_offset_ready_def obj_at_def pred_tcb_at_def not_queued_2_def)
   done

lemma commit_time_valid_release_q_cur_sc_not_in_release_q:
  "\<lbrace>invs and schact_is_rct and valid_release_q and (\<lambda>s. sc_not_in_release_q (cur_sc s) s)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding commit_time_def
  apply (wpsimp wp: sc_consumed_update_sc_tcb_sc_at hoare_vcg_all_lift hoare_drop_imp
                     refill_budget_check_valid_release_q
                     refill_budget_check_round_robin_valid_release_q
         split_del: if_split)
  by clarsimp

lemma refill_budget_check_sc_refills_update_unspecified:
  "\<lbrace>\<lambda>s. \<forall>f. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
              (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
              (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
              (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
              (heap_upd (scrc_refills_update f) (cur_sc s) (sc_refill_cfgs_of s)) (sc_replies_of s)\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  unfolding refill_budget_check_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (wpsimp wp: set_refills_valid_sched_pred)
  done

lemma refill_budget_check_round_robin_sc_refills_update_unspecified:
  "\<lbrace>\<lambda>s. \<forall>f. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
              (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
              (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
              (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
              (heap_upd (scrc_refills_update f) (cur_sc s) (sc_refill_cfgs_of s)) (sc_replies_of s)\<rbrace>
   refill_budget_check_round_robin usage
   \<lbrace>\<lambda>_. valid_sched_pred_strong P\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (wpsimp wp: set_refills_valid_sched_pred)
  done

lemma commit_time_released_ipc_queues[wp]:
  "\<lbrace>released_ipc_queues\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  supply if_split[split del]
  apply (simp add: commit_time_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[where B="\<lambda>_. released_ipc_queues"], wpsimp)
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[where B="\<lambda>_. released_ipc_queues"], wpsimp)
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (rule_tac B="\<lambda>_ s. is_active_sc csc s
                           \<and> (\<forall>t. pred_map_eq (Some csc) (tcb_scps_of s) t
                                  \<or> released_ipc_queued_thread t s)"
           in hoare_seq_ext)
   apply wpsimp
   apply (simp add: released_ipc_queues_defs)
   apply (erule allEI, fastforce simp: obj_at_def vs_all_heap_simps)
  apply (wpsimp wp: refill_budget_check_sc_refills_update_unspecified
                    refill_budget_check_round_robin_sc_refills_update_unspecified)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps)
  apply (simp add: released_ipc_queues_defs)
  apply (erule allEI)
  by (fastforce simp: heap_upd_def vs_all_heap_simps)

lemma commit_time_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
   unfolding commit_time_def
   by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps set_refills_valid_sched_action_act_not
                  refill_budget_check_valid_sched_action_act_not simp: refill_budget_check_round_robin_def
        | strengthen simple_sched_act_not | intro conjI)+

crunches commit_domain_time, refill_budget_check, refill_budget_check_round_robin
  for valid_blocked_except_set[wp]: "valid_blocked_except_set S"
  (wp: crunch_wps simp: crunch_simps)

lemma refill_budget_check_round_robin_not_active_sc[wp]:
   "\<lbrace>(\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp)\<rbrace>
    refill_budget_check_round_robin usage
    \<lbrace>\<lambda>_ s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  supply if_split [split del]
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: valid_sched_wp hoare_drop_imp)

lemma refill_budget_check_not_active_sc[wp]:
   "\<lbrace>(\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp)\<rbrace>
    refill_budget_check usage
    \<lbrace>\<lambda>_ s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  supply if_split [split del]
  unfolding refill_budget_check_def
  by (wpsimp wp: valid_sched_wp hoare_drop_imp)

lemma commit_time_not_active_sc[wp]:
  "\<lbrace>(\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp)\<rbrace>
   commit_time
   \<lbrace>\<lambda>_ s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  apply (clarsimp simp: commit_time_def )
  by (wpsimp wp: hoare_drop_imp)

lemma refill_budget_check_round_robin_bounded_release_time[wp]:
  "\<lbrace>bounded_release_time scp
    and current_time_bounded 1\<rbrace>
   refill_budget_check_round_robin consumed
   \<lbrace>\<lambda>_. bounded_release_time scp\<rbrace>"
 unfolding refill_budget_check_round_robin_def
  apply (wpsimp wp: valid_sched_wp is_round_robin_wp)
  by (auto simp: vs_all_heap_simps bounded_release_time_def pred_map_simps obj_at_def
                 heap_upd_def current_time_bounded_def)

lemma set_refills_bounded_release_time:
  "\<lbrace>bounded_release_time scp
    and (\<lambda>s. sc_ptr = scp \<longrightarrow> bounded_release_time_2 (cur_time s) (r_time (hd rfls)) )\<rbrace>
   set_refills sc_ptr rfls
   \<lbrace>\<lambda>_. bounded_release_time scp\<rbrace>"
  unfolding refill_budget_check_def
  apply (wpsimp wp: valid_sched_wp)
  by (clarsimp simp: vs_all_heap_simps bounded_release_time_def pred_map_simps obj_at_def
                    heap_upd_def split: if_split)

lemma refill_budget_check_bounded_release_time:
  "\<lbrace>bounded_release_time scp
    and (\<lambda>s. \<forall>sc n. kheap s (cur_sc s) = Some (SchedContext sc n) \<longrightarrow>
      ((\<not> sc_refill_ready (cur_time s) sc \<or> r_amount (refill_hd sc) < consumed)
       \<longrightarrow> (cur_sc_offset_ready consumed s) ))
    and current_time_bounded 2
    and valid_refills scp\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. bounded_release_time scp\<rbrace>"
  supply if_split[split del]
  supply schedule_used.simps [simp del]
  unfolding refill_budget_check_def
  apply (wpsimp wp: is_round_robin_wp set_refills_bounded_release_time)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI allI impI)
      (* 5 *)
      apply (clarsimp simp: cur_sc_offset_ready_def obj_at_def bounded_release_time_def current_time_bounded_def)
      apply (rule_tac y="(unat (r_time (refill_hd sc)) + unat consumed) + unat (sc_period sc)"
             in order_trans[rotated])
       apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
      apply (rule order_trans, rule unat_plus_gt)
      apply (rule order_trans, rule add_le_mono1, rule unat_plus_gt)
      apply simp
     (* 4 *)
     apply (simp add: bounded_release_time_2_def)
     apply (frule sc_refill_ready_release_time_well_bounded, simp+)
     apply (rule order_trans)
      apply (rule iffD1[OF word_le_nat_alt])
      apply (rule schedule_used_release_time_bounded; clarsimp)
       apply (rule sc_valid_refills_times_bounded)
         apply (clarsimp simp: obj_at_def valid_refills_def2)
        apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
        apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
       apply (metis Suc_length_not_empty hd_in_set list.set_sel(2) nat_less_le tail_nonempty_length)
      apply (overflow_hammer)
      apply (subst add.commute)
      apply (rule order_trans[rotated], rule no_plus_overflow_unat_size2, overflow_hammer)
       apply (subst add.commute)
       apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
       prefer 2
       apply (rule sc_valid_refills_amounts_bounded)
        apply (clarsimp simp: valid_refills_def2)
       apply (metis Suc_length_not_empty hd_in_set list.set_sel(2) nat_less_le tail_nonempty_length)
      apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
     apply (clarsimp simp: refill_ready_def)
     apply (rule order_trans[OF unat_plus_gt])
     apply (rule add_mono[rotated])
      apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
     apply (clarsimp simp: unat_le_mono current_time_bounded_def)
     apply (erule order_trans, rule unat_plus_gt)
    (* 3 *)
    apply (frule sc_refill_ready_release_time_well_bounded, simp+)
    apply (clarsimp simp: obj_at_def refill_ready_def bounded_release_time_2_def)
    apply (rule_tac y="unat (r_time (refill_hd sc)) + unat (sc_period sc)" in order_trans[rotated])
     apply (rule add_mono[rotated])
      apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
     apply (clarsimp simp: unat_le_mono)
     apply (erule order_trans, rule unat_plus_gt)
    apply (rule order_trans[rotated], rule unat_plus_gt)
    apply (clarsimp simp: unat_le_mono[symmetric], overflow_hammer)
    apply (rule order_trans, rule word_sub_le, simp)
    apply (simp add: add.commute)
    apply (rule order_trans[rotated], rule no_plus_overflow_unat_size2, overflow_hammer)
     apply (subst add.commute)
     apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
     apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
    apply (clarsimp simp: valid_refills_def2)
    apply (rule sc_valid_refills_amounts_bounded, simp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
   (* 2 *)
   apply (frule sc_refill_ready_release_time_well_bounded, simp+)
   apply (clarsimp simp: vs_all_heap_simps bounded_release_time_def pred_map_simps obj_at_def
                     heap_upd_def Let_def split: if_split)
   apply (rule order_trans)
    apply (rule iffD1[OF word_le_nat_alt])
    apply (rule schedule_used_release_time_bounded; simp)
     apply (rule_tac y="r_time (hd (tl (sc_refills sc)))" in order_trans, overflow_hammer)
      apply (rule_tac y="r_time (hd ((sc_refills sc))) + r_amount (hd ((sc_refills sc)))" in order_trans)
       apply (rule_tac order_trans, erule order.strict_implies_order)
       apply (rule_tac y="r_amount (hd ((sc_refills sc)))" in order_trans)
        apply (fastforce intro: sc_valid_refills_amounts_bounded_below sc_valid_refills_hd_in_list)
       apply (overflow_hammer)
       apply (fastforce intro: sc_valid_refills_no_overflow sc_valid_refills_hd_in_list)
      apply (clarsimp simp: sc_valid_refills_def ordered_disjoint_def )
      apply (subst word_le_nat_alt)
      apply (rule_tac order_trans, rule unat_plus_gt)
      apply (drule_tac x=0 in spec, simp add: hd_conv_nth nth_tl tail_nonempty_length)
     apply (rule sc_valid_refills_times_bounded, simp)
      apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
      apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
     apply (fastforce intro: list.set_sel)
    apply (rule order_trans)
     apply (rule word_sub_le)
     apply (rule_tac y="sc_period sc" in order_trans)
      apply (rule_tac y="refills_sum (sc_refills sc)" in order_trans)
       apply (rule_tac y="r_amount (hd (tl (sc_refills sc))) + r_amount (refill_hd sc)" in order_trans)
        apply (rule word_plus_mono_right, overflow_hammer, simp)
        apply (overflow_hammer)
        apply (rule_tac y="unat (refills_sum (sc_refills sc))" in order_trans)
         apply (simp add: word_le_nat_alt refills_sum_def)
         apply (subst valid_refills_unat_sum_list; clarsimp simp: valid_refills_def)
         apply (case_tac "sc_refills sc"; simp)
         apply (case_tac "list"; simp)
        apply (clarsimp simp: word_le_nat_alt[symmetric])
       apply (simp add: word_le_nat_alt refills_sum_def)
       apply (subst valid_refills_unat_sum_list; clarsimp simp: valid_refills_def)
       apply (rule order_trans[OF unat_plus_gt])
       apply (case_tac "sc_refills sc"; simp)
       apply (case_tac "list"; simp)
      apply (simp add: valid_refills_def)
     apply (overflow_hammer)
     apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
     apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
    apply simp
   apply simp
   apply (rule order_trans, rule unat_plus_gt)
   apply (rule add_mono)
    apply (clarsimp simp: refill_ready_def unat_le_mono)
    apply (erule order_trans, rule unat_plus_gt)
   apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
  (* 1 *)
  apply (frule sc_refill_ready_release_time_well_bounded, simp+)
  apply (clarsimp simp: vs_all_heap_simps bounded_release_time_def pred_map_simps obj_at_def
                    heap_upd_def Let_def split: if_split)
  apply (rule order_trans)
   apply (rule iffD1[OF word_le_nat_alt])
   apply (rule schedule_used_release_time_bounded; simp)
    apply (rule word_plus_mono_right)
     apply (subgoal_tac "r_amount (refill_hd sc) \<le> sc_period sc", simp)
     apply (fastforce intro: sc_valid_refills_amounts_bounded sc_valid_refills_hd_in_list)
    apply (overflow_hammer)
    apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
   apply (overflow_hammer)
   apply (rule order_trans, rule word_sub_le, simp)
   apply (simp add: add.commute)
   apply (rule order_trans[rotated], rule no_plus_overflow_unat_size2, overflow_hammer)
    apply (subgoal_tac "unat (sc_period sc) \<le> unat MAX_SC_PERIOD", simp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
   apply (rule sc_valid_refills_amounts_bounded, simp)
   apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
  apply simp
  apply (rule order_trans, rule unat_plus_gt)
  apply (rule add_mono)
   apply (clarsimp simp: refill_ready_def unat_le_mono)
   apply (erule order_trans, rule unat_plus_gt)
  apply (clarsimp simp: valid_refills_def vs_all_heap_simps unat_le_mono)
  done

lemma refill_budget_check_round_robin_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and K (unat consumed + unat MAX_SC_PERIOD \<le> unat max_time)
    and current_time_bounded 1\<rbrace>
   refill_budget_check_round_robin consumed
   \<lbrace>\<lambda>_. active_sc_valid_refills\<rbrace>"
  unfolding active_sc_valid_refills_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma cur_sc_bounded_release_helper:
  "kheap s (cur_sc s) = Some (SchedContext sc n)
  \<Longrightarrow> sc_period sc \<le> MAX_SC_PERIOD
  \<Longrightarrow> unat (r_time (refill_hd sc)) + unat (sc_period sc) + unat MAX_SC_PERIOD + unat consumed \<le> unat max_time
  \<Longrightarrow> unat (r_time (refill_hd sc)) + 2 * unat (sc_period sc) + unat consumed \<le> unat max_time"
  by (simp add: unat_le_mono)

lemma refill_budget_check_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and (\<lambda>s. (\<forall>sc. (\<exists>n. kheap s (cur_sc s) = Some (SchedContext sc n)) \<longrightarrow>
                      (sc_refill_ready (cur_time s) sc \<longrightarrow>
                       r_amount (refill_hd sc) < consumed) \<longrightarrow>
                      cur_sc_offset_ready consumed s))
    and current_time_bounded 2\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. active_sc_valid_refills\<rbrace>"
  unfolding active_sc_valid_refills_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift
                          refill_budget_check_bounded_release_time)
  done

(* These complicated preconditions maybe slightly improved since we should know that
   the cur_sc is ready at this point *)
lemma commit_time_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and cur_sc_in_release_q_imp_zero_consumed
    and (\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
    and current_time_bounded 2
    and consumed_time_bounded\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. active_sc_valid_refills\<rbrace>"
  unfolding commit_time_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[where B="\<lambda>_. active_sc_valid_refills"], wpsimp)
  apply clarsimp
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[where B="\<lambda>_. active_sc_valid_refills"], wpsimp)
  apply (rule hoare_when_cases, simp)
  apply (wpsimp wp: assert_inv
                    refill_budget_check_round_robin_active_sc_valid_refills
                    refill_budget_check_active_sc_valid_refills)
      apply (wpsimp wp: assert_inv is_round_robin_wp)+
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "cur_sc_active s")
  apply (fastforce intro: current_time_bounded_strengthen consumed_time_bounded_helper)
  apply (clarsimp simp: vs_all_heap_simps)
  done

lemma commit_time_valid_blocked_except_set[wp]:
  "commit_time \<lbrace>valid_blocked_except_set S\<rbrace>"
  unfolding commit_time_def
  by (wpsimp wp: hoare_drop_imps)

lemma refill_budget_check_active_reply_scs[wp]:
  "refill_budget_check usage \<lbrace>active_reply_scs\<rbrace>"
  by (wpsimp wp: refill_budget_check_sc_refills_update_unspecified
           simp: active_reply_scs_defs)

lemma refill_budget_check_round_robin_active_reply_scs[wp]:
  "refill_budget_check_round_robin usage \<lbrace>active_reply_scs\<rbrace>"
  by (wpsimp wp: refill_budget_check_round_robin_sc_refills_update_unspecified
           simp: active_reply_scs_defs)

lemma commit_time_active_reply_scs[wp]:
  "commit_time \<lbrace>active_reply_scs\<rbrace>"
  unfolding commit_time_def by (wpsimp wp: hoare_drop_imps)

lemma commit_time_valid_sched:
  "\<lbrace>valid_sched
    and simple_sched_action
    and cur_sc_in_release_q_imp_zero_consumed
    and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)
    and (\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
    and current_time_bounded 2
    and consumed_time_bounded
    and valid_state\<rbrace>
   commit_time
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
   unfolding valid_sched_def
   by (wpsimp wp: commit_time_valid_release_q commit_time_active_sc_valid_refills
                  commit_time_valid_ready_qs commit_time_valid_sched_action)

(* end commit_time *)

(* refill_unblock_check *)

lemma r_time_hd_refills_merge_prefix:
  "r_time (hd (refills_merge_prefix (a # l))) = r_time a"
  by (induct l arbitrary: a;
      clarsimp simp: merge_refill_def)

lemma refill_unblock_check_valid_sched_misc[wp]:
  "refill_unblock_check scptr
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: hoare_drop_imp)

lemma r_amount_hd_refills_merge_prefix:
  "sum_list (map unat (map r_amount (a # ls))) \<le> unat max_time
   \<Longrightarrow> r_amount a \<le> r_amount (hd (refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls)))"
  supply map_map[simp del]
  apply (induct ls arbitrary: a)
   apply force
  apply simp
  apply (intro impI)
  apply (drule_tac x="merge_refill (aa\<lparr>r_time := new_time\<rparr>) a" in meta_spec)
  apply (simp add: can_merge_refill_def merge_refill_def word_le_nat_alt)
  apply (subgoal_tac "unat (r_amount a + r_amount aa) = unat (r_amount a) + unat (r_amount aa)")
   apply linarith
  apply (rule unat_add_lem', simp add: max_word_def)
  done

lemma refills_merge_prefix_refills_sum:
  "refills_sum (refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls)) = refills_sum (a # ls)"
  apply (induction ls arbitrary: a)
   apply simp
  apply (drule_tac x="merge_refill (aa\<lparr>r_time := new_time\<rparr>) a" in meta_spec)
  apply (simp add: merge_refill_def)
  done

lemma refills_merge_prefix_ordered_disjoint:
  "\<lbrakk>ordered_disjoint ls;
    unat new_time + sum_list (map unat (map r_amount (a # ls))) \<le> unat max_time\<rbrakk>
   \<Longrightarrow> ordered_disjoint (refills_merge_prefix ( a\<lparr>r_time := new_time\<rparr> # ls))"
  supply map_map[simp del]
  apply (induction ls arbitrary: a rule: length_induct)
  apply (case_tac xs)
   apply (simp add: ordered_disjoint_def)
  apply simp
  apply (intro conjI impI)

   \<comment> \<open>can merge first two refills\<close>
   apply (simp add: can_merge_refill_def merge_refill_def)
   apply (drule_tac x=list in spec)
   apply clarsimp
   apply (elim impE)
    using ordered_disjoint_tail apply blast
   apply (drule_tac x="merge_refill a aa" in spec)
   apply (simp add: merge_refill_def)
   apply (subgoal_tac "unat (r_amount aa + r_amount a) = unat (r_amount aa) + unat (r_amount a)")
    apply linarith
   apply (rule unat_add_lem', simp add: max_word_def)

  \<comment> \<open>cannot merge first two refills\<close>
  apply (simp add: can_merge_refill_def merge_refill_def)
  apply (simp add: word_not_le)
  apply (rule_tac left="[a\<lparr>r_time := new_time\<rparr>]" and right="aa # list" in ordered_disjoint_append)
     apply (simp add: ordered_disjoint_def)
    using ordered_disjoint_tail apply blast
   apply (intro conjI impI)
   apply clarsimp
   apply (simp add: word_less_nat_alt)
   apply (subgoal_tac "unat (new_time + r_amount a) = unat new_time + unat (r_amount a)")
    apply linarith
   apply (rule unat_add_lem', simp add: max_word_def)
  apply simp
  done

lemma refills_merge_prefix_no_overflow:
  "\<lbrakk>unat new_time + sum_list (map unat (map r_amount (a # ls))) \<le> unat max_time;
    no_overflow ls\<rbrakk>
   \<Longrightarrow> no_overflow (refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls))"
  supply map_map[simp del]
  apply (induction ls arbitrary: a rule: length_induct)
  apply (case_tac xs)
   apply (simp add: no_overflow_def)
  apply simp
  apply (intro conjI impI)

   \<comment> \<open>can merge first two refills\<close>
   apply (simp add: can_merge_refill_def merge_refill_def)
   apply (drule_tac x=list in spec)
   apply clarsimp
   apply (drule_tac x="merge_refill a aa" in spec)
   apply (simp add: can_merge_refill_def merge_refill_def)
   apply (elim impE)
     apply (subgoal_tac "unat (r_amount aa + r_amount a) = unat (r_amount aa) + unat (r_amount a)")
      apply linarith
     apply (rule unat_add_lem', simp add: max_word_def)
    using no_overflow_tail apply fast
   apply blast

  \<comment> \<open>cannot merge first two refills\<close>
  apply (rule_tac left="[a\<lparr>r_time := new_time\<rparr>]" and right="aa # list" in no_overflow_append)
    apply (simp add: no_overflow_def)
   using no_overflow_tail apply fast
  by force

lemma refills_merge_prefix_MIN_BUDGET:
  "\<lbrakk>\<forall>m < length (a # ls). MIN_BUDGET \<le> r_amount ((a # ls) ! m);
    unat new_time + sum_list (map unat (map r_amount (a # ls))) \<le> unat max_time\<rbrakk>
   \<Longrightarrow> \<forall>m < length (refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls)).
              MIN_BUDGET \<le> r_amount ((refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls)) ! m)"
  supply map_map[simp del]
  apply (induction ls arbitrary: a rule: length_induct)
  apply (case_tac xs)
   apply fastforce
  apply (clarsimp simp: if_splits)
  apply (intro conjI impI)
   apply clarsimp
   apply (drule_tac x=list in spec)
   apply (simp add: can_merge_refill_def merge_refill_def)
   apply (drule_tac x="\<lparr>r_time = new_time, r_amount = r_amount aa + r_amount a\<rparr>" in spec)
   apply clarsimp
   apply (elim impE)
     apply clarsimp
     apply (case_tac "ma=0")
      apply clarsimp
      apply (simp add: word_le_nat_alt)
      apply (subgoal_tac "unat (r_amount aa + r_amount a) = unat (r_amount aa) + unat (r_amount a)")
       apply force
      apply (rule unat_add_lem', simp add: max_word_def)
     apply force
    apply (subgoal_tac "unat (r_amount aa + r_amount a) = unat (r_amount aa) + unat (r_amount a)")
     apply linarith
    apply (rule unat_add_lem', simp add: max_word_def)
   apply blast
  apply (clarsimp simp: can_merge_refill_def merge_refill_def)
  apply (case_tac "m=0"; fastforce)
  done

lemma refills_merge_prefix_window:
  "\<lbrakk>r_time a \<le> new_time;
    unat new_time + sum_list (map unat (map r_amount (a # ls))) \<le> unat max_time;
    sum_list (map unat (map r_amount (a # ls))) \<le> unat period;
    window (a # ls) period\<rbrakk>
   \<Longrightarrow> window (refills_merge_prefix (a\<lparr>r_time := new_time\<rparr> # ls)) period"
  supply map_map[simp del]
  apply (induction ls arbitrary: a rule: length_induct)
  apply (case_tac xs)
   apply (simp add: window_def)
  apply (rename_tac xs a aa list)

  \<comment> \<open>a useful fact\<close>
  apply (subgoal_tac "unat (r_amount aa + r_amount a) = unat (r_amount aa) + unat (r_amount a)")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)
  \<comment> \<open>end of the proof of the useful fact\<close>

  apply simp
  apply (intro conjI impI)

   \<comment> \<open>can merge first two refills\<close>
   apply (drule_tac x=list in spec)
   apply clarsimp
   apply (drule_tac x="\<lparr>r_time = new_time, r_amount = r_amount aa + r_amount a\<rparr>" in spec)
   apply (elim impE; clarsimp?)
    apply (clarsimp simp: window_def word_le_nat_alt split: if_splits)
   apply (clarsimp simp: can_merge_refill_def merge_refill_def word_le_nat_alt)

  \<comment> \<open>cannot merge first two refills\<close>
  using word_le_nat_alt window_def by force

lemma refills_merge_prefix_length:
  "length (refills_merge_prefix ls) \<le> length ls"
  by (induct ls rule: refills_merge_prefix.induct) fastforce+

lemma refill_unblock_check_valid_refills[wp]:
   "\<lbrace>(\<lambda>s. scp = p \<longrightarrow> (\<forall>sc n. kheap s scp = Some (SchedContext sc n) \<longrightarrow>
          unat (r_amount (refill_hd sc)) + unat (cur_time s) + unat kernelWCET_ticks
                     \<le> unat max_time
          \<and> unat (cur_time s) + unat kernelWCET_ticks + unat (sc_budget sc)
                     \<le> unat max_time))
      and valid_refills p\<rbrace>
    refill_unblock_check scp
    \<lbrace>\<lambda>_. valid_refills p\<rbrace>"
  supply map_map[simp del]
  apply (case_tac "scp \<noteq> p")
   apply (simp add: refill_unblock_check_def is_round_robin_def)
   apply (wpsimp simp: set_refills_def update_sched_context_def valid_refills_def obj_at_def
                   wp: set_object_wp get_object_wp get_refills_wp)
  apply (clarsimp simp: valid_refills_def vs_all_heap_simps)

  apply (simp add: refill_unblock_check_def is_round_robin_def)
  apply (wpsimp simp: set_refills_def update_sched_context_def
                  wp: set_object_wp get_object_wp get_refills_wp)
  apply (clarsimp simp: obj_at_def refill_ready_def)

  \<comment> \<open>some useful facts\<close>
  apply (subgoal_tac "unat (cur_time s + kernelWCET_ticks)
                      = unat (cur_time s) + unat kernelWCET_ticks")
   prefer 2
   apply (rule unat_add_lem', simp add: max_word_def)

   apply (subgoal_tac "unat (r_amount (refill_hd sc) + cur_time s + kernelWCET_ticks)
                      = unat (r_amount (refill_hd sc)) + unat (cur_time s) + unat kernelWCET_ticks")
   prefer 2
   apply (subgoal_tac "unat (r_amount (refill_hd sc) + cur_time s + kernelWCET_ticks)
                       = unat (r_amount (refill_hd sc) + cur_time s) + unat kernelWCET_ticks")
    apply clarsimp
    apply (rule unat_add_lem', simp add: max_word_def)
   apply (rule unat_add_lem')
   apply (subgoal_tac "unat (r_amount (refill_hd sc) + cur_time s)
                       = unat (r_amount (refill_hd sc)) + unat (cur_time s)")
    apply (simp add: max_word_def)
   apply (rule unat_add_lem', simp add: max_word_def)
  \<comment> \<open>end of the proof of the useful facts\<close>

  apply (intro conjI impI)

    \<comment> \<open>first branch of refill_unblock_check\<close>
    apply (simp add: valid_refills_def vs_all_heap_simps obj_at_def)
    apply (intro conjI impI)
        apply (case_tac "sc_refills sc", fastforce, simp)
       apply (simp add: ordered_disjoint_def)
      apply (simp add: no_overflow_def)
      apply (case_tac "sc_refills sc", blast, force)
    apply (simp add: window_def)
    apply (case_tac "sc_refills sc", argo, force)
   apply simp

   \<comment> \<open>second branch of refill_unblock_check\<close>
   apply (simp add: valid_refills_def vs_all_heap_simps obj_at_def)
   apply (elim conjE)

   \<comment> \<open>a useful fact\<close>
   apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
          ; (simp add: refills_sum_def)?)
     using MIN_BUDGET_pos unat_gt_0 apply fastforce
    using MIN_BUDGET_le_MIN_SC_BUDGET apply force
   \<comment> \<open>end of the proof of the useful fact\<close>

   apply (intro conjI impI)
       apply (case_tac "sc_refills sc", fastforce, case_tac list, simp, simp add: word_le_nat_alt)
      apply (simp add: ordered_disjoint_def)
     apply (simp add: no_overflow_def)
     apply clarsimp
     apply (case_tac "na=0")
      apply clarsimp
     apply (case_tac "sc_refills sc", fastforce, case_tac list, simp, simp add: word_le_nat_alt)
    apply clarsimp
    apply (case_tac "na=0")
     apply (simp add: hd_conv_nth)
    apply clarsimp
    apply (metis Nitpick.size_list_simp(2) double_not_eq_Suc_double hd_conv_nth
                 length_greater_0_conv less_2_cases mult_2 nth_tl numeral_2_eq_2 numeral_Bit0)
   apply (simp add: window_def)
   apply (case_tac "sc_refills sc", blast, case_tac list, simp, simp)

  \<comment> \<open>last branch of refill_budget_check\<close>
  apply (simp add: valid_refills_def vs_all_heap_simps obj_at_def)
  apply (elim conjE)

   \<comment> \<open>a useful fact\<close>
  apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
         ; simp?)
    using MIN_BUDGET_pos unat_gt_0 apply fastforce
   using MIN_BUDGET_le_MIN_SC_BUDGET apply force
   \<comment> \<open>end of the proof of the useful fact\<close>

  apply (intro conjI impI)
        apply (simp add: refills_merge_prefix_refills_sum)
       apply (rule refills_merge_prefix_ordered_disjoint)
        apply (metis list.exhaust_sel ordered_disjoint_tail)
       apply clarsimp
      apply (rule refills_merge_prefix_no_overflow)
       apply clarsimp
      apply (metis no_overflow_tail list.exhaust_sel)
     apply (rule refills_merge_prefix_MIN_BUDGET; fastforce)
    apply (erule_tac new_time="cur_time s + kernelWCET_ticks" in refills_merge_prefix_window
           ; fastforce simp: word_le_nat_alt)
   apply (metis refills_merge_valid list.sel(3) list.simps(3) list.size(3) non_empty_tail_length
                not_one_le_zero numeral_nat(7) refills_merge_prefix.simps(2))
  apply (metis refills_merge_prefix_length Nitpick.size_list_simp(2) Suc_length_conv le_trans)
  done

lemma refill_unblock_check_budget_ready[wp]:
  "\<lbrace>budget_ready tcb_ptr and valid_machine_time\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_ready tcb_ptr s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_def refill_ready_def)
  apply (intro conjI impI, fastforce)
      apply fastforce
     apply (clarsimp simp: r_time_hd_refills_merge_prefix)
    apply (rule_tac x=ref' in exI; clarsimp)
   apply (rule_tac x=ref' in exI; clarsimp)
  apply (rule_tac x=ref' in exI; clarsimp)
  apply (clarsimp simp: r_time_hd_refills_merge_prefix)
  done

lemma refill_unblock_check_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient tcb_ptr and active_sc_tcb_at tcb_ptr and active_sc_valid_refills\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_sufficient tcb_ptr s\<rbrace>"
  supply map_map[simp del]
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (frule (1) active_implies_valid_refills_tcb_at)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps is_refill_sufficient_def
                        refill_sufficient_defs)
  apply (intro conjI impI)
       apply clarsimp+
    apply fastforce
   apply fastforce
  apply (rule_tac x=ref'a in exI; clarsimp)
  apply (erule_tac y="r_amount (refill_hd sc)" in order_trans)
  apply (rule r_amount_hd_refills_merge_prefix)
  apply (subgoal_tac "sc_valid_refills sc")
   apply (simp add: sc_valid_refills_def, elim conjE)
   apply (frule_tac refills="sc_refills sc" in unat_sum_list_equals_budget
          ; (simp add: refills_sum_def)?)
  using MIN_BUDGET_pos unat_gt_0 apply fastforce
  using MIN_BUDGET_le_MIN_SC_BUDGET apply fastforce
  using word_le_nat_alt apply fastforce
  apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_refills_def sc_at_pred_n_def)
  done

lemma refill_unblock_check_active_sc_tcb_at[wp]:
  "\<lbrace> active_sc_tcb_at x\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r. active_sc_tcb_at x\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  by (fastforce simp: vs_all_heap_simps obj_at_def)

lemma refill_unblock_check_released_sc_tcb_at[wp]:
  "\<lbrace>released_sc_tcb_at x and valid_machine_time and active_sc_valid_refills\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>r. released_sc_tcb_at x\<rbrace>"
  unfolding released_sc_tcb_at_def
  by wpsimp

lemma refill_unblock_check_valid_ready_qs[wp]:
  "\<lbrace> valid_ready_qs and valid_machine_time and active_sc_valid_refills\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>_. valid_ready_qs\<rbrace>"
  apply (clarsimp simp: valid_ready_qs_def )
  apply (wpsimp simp: Ball_def released_sc_tcb_at_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift''
                      refill_unblock_check_active_sc_tcb_at)
  done

lemma update_sched_context_tcb_ready_times_idem:
  assumes "Q t"
  assumes "\<And>sc. sc_refill_cfg_of (f sc) = g (sc_refill_cfg_of sc)"
  assumes "\<And>sc. sc_tcb (f sc) = h (sc_tcb sc)"
  assumes "\<And>sc. sc_replies (f sc) = k (sc_replies sc)"
  shows "\<lbrace>\<lambda>s. P (tcb_ready_times_of s t) \<and> sc_with_tcb_prop sc_ptr (\<lambda>t s. \<not> Q t) s\<rbrace>
         update_sched_context sc_ptr f
         \<lbrace>\<lambda>_ s. P (tcb_ready_times_of s t)\<rbrace>"
  apply (wpsimp wp: update_sched_context_valid_sched_pred'
                    [where g=g and f=f and h=h and k=k, OF assms(2-4), THEN hoare_drop_assertion])
  using assms
  by (fastforce simp: heap_upd_def tcb_ready_times_defs
                      map_project_simps opt_map_simps map_join_simps vs_all_heap_simps
               split: if_splits
               elim!: rsubst[of P]
              intro!: option_eqI[where opt'="map_project _ _ _"])

lemma refill_unblock_check_sorted_release_q:
  "\<lbrace>\<lambda>s. sorted_release_q s \<and> sc_not_in_release_q sc_ptr s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. sorted_release_q\<rbrace>"
  supply if_split[split del]
  apply (rule hoare_lift_Pf2[where f=release_queue, rotated], wpsimp)
  apply (rule sorted_release_q_2_valid_lift)
  apply (simp add: refill_unblock_check_def)
  apply (intro hoare_seq_ext_skip hoare_if hoare_when_cases; (solves \<open>wpsimp wp:\<close>)?)
    unfolding set_refills_def
    apply (rule update_sched_context_tcb_ready_times_idem; simp add: in_queue_2_def)+
  done

lemma refill_unblock_check_valid_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding valid_release_q_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_unblock_check_sorted_release_q
           simp: Ball_def)

lemma ruc_not_pred_map_sc_active[wp]:
  "refill_unblock_check sc_ptr \<lbrace>\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: valid_sched_wp hoare_drop_imp)

lemma refill_unblock_check_bounded_release_time:
  "\<lbrace>bounded_release_time scp
    and current_time_bounded 1
    and valid_machine_time\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. bounded_release_time scp\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_bounded_release_time get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: obj_at_def r_time_hd_refills_merge_prefix current_time_bounded_def
                        bounded_release_time_def)
  apply (subgoal_tac "unat (cur_time s + kernelWCET_ticks)
              \<le> unat (cur_time s) + unat kernelWCET_ticks + unat MAX_SC_PERIOD", clarsimp)
  by (rule order_trans, rule unat_plus_gt, simp)

lemma refill_unblock_check_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and current_time_bounded 1
    and valid_machine_time\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. active_sc_valid_refills\<rbrace>"
  unfolding active_sc_valid_refills_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_unblock_check_bounded_release_time
              simp: Ball_def)
  apply (simp add: current_time_bounded_def)
  apply (intro conjI)
   apply (erule_tac order_trans[rotated])
   apply (rule_tac y="unat (cur_time s) + unat kernelWCET_ticks + unat (r_amount (refill_hd sc))"
          in order_trans)
    apply fastforce
   apply (rule add_left_mono)
   apply (rule_tac y="unat (sc_budget sc)" in order_trans[rotated])
    apply (drule_tac x=sc_ptr in spec, simp)
    apply (clarsimp simp: valid_refills_def vs_all_heap_simps word_le_nat_alt[symmetric], fastforce)
   apply (drule_tac x=sc_ptr in spec, simp)
   apply (clarsimp simp: valid_refills_def vs_all_heap_simps word_le_nat_alt[symmetric])
   apply (rule valid_refills_r_amount_bounded_sc_budget, clarsimp simp: sc_valid_refills_def)
  apply (erule_tac order_trans[rotated])
  apply (rule add_left_mono)
  apply (drule_tac x=sc_ptr in spec, simp)
  apply (clarsimp simp: valid_refills_def vs_all_heap_simps word_le_nat_alt[symmetric], fastforce)
  done

lemma refill_unblock_check_valid_blocked_except_set[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: vs_all_heap_simps valid_blocked_except_set_2_def valid_blocked_thread_def)
  apply (intro conjI impI allI
         ; drule_tac x=t in spec, fastforce simp: obj_at_def)
  done

lemmas refill_unblock_check_valid_blocked[wp] =
       refill_unblock_check_valid_blocked_except_set[where S="{}"]

lemma ready_or_release_reprogram_timer_update[simp]:
  "ready_or_release (s\<lparr>reprogram_timer := b\<rparr>)
          = ready_or_release s"
  by (clarsimp simp: ready_or_release_def)

crunches refill_unblock_check
  for sc_at_period[wp]: "sc_at_period P p"
  and sc_at_period_sc[wp]: "\<lambda>s. sc_at_period P (cur_sc s) s"
    (wp: crunch_wps simp: crunch_simps)

lemma refill_unblock_check_sc_is_round_robin[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin p s)\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_is_round_robin p s)\<rbrace>"
  unfolding refill_unblock_check_def is_round_robin_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  by (fastforce simp: sc_is_round_robin_def obj_at_def sc_at_pred_n_def)

lemma refill_unblock_check_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and active_sc_valid_refills
    and valid_machine_time\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (clarsimp simp: is_activatable_def weak_valid_sched_action_def switch_in_cur_domain_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift''
                    refill_unblock_check_st_tcb_at)
  done

lemma refill_unblock_check_released_ipc_queues[wp]:
  "\<lbrace>released_ipc_queues and valid_machine_time and active_sc_valid_refills\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  unfolding released_ipc_queues_defs
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift''
                 refill_unblock_check_st_tcb_at hoare_vcg_disj_lift)

lemma refill_unblock_check_active_reply_scs[wp]:
  "refill_unblock_check scp \<lbrace>active_reply_scs\<rbrace>"
  unfolding refill_unblock_check_def by (wpsimp wp: hoare_drop_imps)

lemma refill_unblock_check_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and sc_not_in_release_q sc_ptr and current_time_bounded 1\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: refill_unblock_check_valid_ready_qs refill_unblock_check_valid_release_q
                 refill_unblock_check_valid_sched_action refill_unblock_check_active_sc_valid_refills)

lemma refill_unblock_check_valid_sched:
  "\<lbrace>valid_sched and sc_not_in_release_q sc_ptr and current_time_bounded 1\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: refill_unblock_check_valid_ready_qs
                 refill_unblock_check_valid_release_q
                 refill_unblock_check_valid_sched_action
                 refill_unblock_check_active_sc_valid_refills)

lemma refill_unblock_check_sc_is_round_robin_ct[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

lemma refill_unblock_check_cur_sc_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. sc_ptr \<noteq> cur_sc s \<and> cur_sc_budget_sufficient s\<rbrace>
  refill_unblock_check sc_ptr
   \<lbrace>\<lambda>_ s. cur_sc_budget_sufficient s\<rbrace>"
  unfolding refill_unblock_check_def is_round_robin_def refill_ready_def
  apply (wpsimp wp: hoare_vcg_all_lift get_refills_wp set_refills_wp)
  by (clarsimp simp: vs_all_heap_simps)

(* end refill_unblock_check *)

lemma sc_is_round_robin_reprogram_timer_update[simp]:
  "sc_is_round_robin p (s\<lparr>reprogram_timer := b\<rparr>)
          = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma ready_or_release_updates[simp]:
  "ready_or_release (trans_state a s) = ready_or_release s"
  by (simp add: ready_or_release_def)+

context DetSchedSchedule_AI begin

lemma ruc_refill_ready_no_overflow_sc:
  "\<lbrace>\<lambda>s. pred_map (refill_ready_no_overflow_sc usage curtime) (sc_refill_cfgs_of s) sc' \<and> sc' \<noteq> sc\<rbrace>
   refill_unblock_check sc
   \<lbrace>\<lambda>_ s. pred_map (refill_ready_no_overflow_sc usage curtime) (sc_refill_cfgs_of s) sc'\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp hoare_drop_imp hoare_vcg_all_lift)
  by (clarsimp simp: vs_all_heap_simps)

lemma ruc_cur_sc_offset_ready_indep[wp]:
  "\<lbrace>(\<lambda>s. a \<noteq> cur_sc s)
    and (\<lambda>s. (sc_not_in_release_q (cur_sc s) s \<longrightarrow>
                 cur_sc_offset_ready (consumed_time s) s))\<rbrace>
   refill_unblock_check a
   \<lbrace>\<lambda>_ s. (sc_not_in_release_q (cur_sc s) s \<longrightarrow>
                 cur_sc_offset_ready (consumed_time s) s)\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift' ruc_refill_ready_no_overflow_sc | wps)+

lemma refill_unblock_check_cur_sc_active[wp]:
  "refill_unblock_check a \<lbrace>cur_sc_active\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: valid_sched_wp get_refills_wp is_round_robin_wp)

lemma switch_sched_context_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and ct_not_in_release_q and ct_not_queued
     and valid_state and ready_or_release
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
     and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)
     and current_time_bounded 2
     and consumed_time_bounded\<rbrace>
   switch_sched_context
   \<lbrace>\<lambda>_. valid_sched :: ('state_ext state) \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: switch_sched_context_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp simp: bind_assoc)
  apply (wpsimp wp: hoare_drop_imp commit_time_valid_sched)
      apply (wpsimp wp: refill_unblock_check_valid_sched)
     apply (wpsimp wp: refill_unblock_check_valid_sched hoare_drop_imp)
    apply wpsimp+
  apply (clarsimp cong: conj_cong)
  apply (intro conjI; simp?)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def vs_all_heap_simps obj_at_kh_kheap_simps cong: conj_cong)
    apply (drule valid_state_sym_refs)
    apply (drule sym[where s="Some _" and t="tcb_sched_context _"])
    apply (frule (1) sym_ref_tcb_sc, simp, clarsimp)
    apply (frule_tac tp=t in sym_ref_tcb_sc, simp, simp)
    apply (clarsimp simp: valid_state_def valid_pspace_def)
   apply (erule current_time_bounded_strengthen, simp)
  apply (clarsimp simp: valid_state_def)
  done

lemma sc_and_timer_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and ct_not_in_release_q and ct_not_queued
     and valid_state and cur_tcb and ready_or_release
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
     and (\<lambda>s. sc_not_in_ready_q (cur_sc s) s)
     and current_time_bounded 2
     and consumed_time_bounded\<rbrace>
   sc_and_timer
   \<lbrace>\<lambda>_. valid_sched :: ('state_ext state) \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sc_and_timer_def)
  by (wpsimp simp: wp: switch_sched_context_valid_sched)

(*
we know that after calling awaken,
all threads in the release queue are either not sufficient or ready
the current thread can be in the release queue
*)

(* FIXME: remove.
   Currently only mentioned by commented out schedule_valid_sched_helper.
   And if rephrased using heap projections, it's just a specialisation of existing [wp] rules. *)
lemma schedule_tcb_sched_enqueue_helper:
  "tcb_sched_action tcb_sched_enqueue ct
   \<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp \<and> is_refill_ready scp s
                                                \<and> is_refill_sufficient 0 scp s)
                        candidate s\<rbrace>"
  by (wpsimp simp: obj_at_kh_kheap_simps)

(* FIXME: this should be expressed more elegantly *)
lemma enqueue_thread_queued_ct:
  "\<lbrace>\<lambda>s. thread = cur_thread s \<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. cur_thread s \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp wp: set_tcb_queue_wp simp: thread_get_def)
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def obj_at_def pred_tcb_at_def
                        is_refill_ready_def is_refill_sufficient_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

lemma cur_sc_tcb_rev:
  "\<lbrakk>cur_sc_tcb s; sym_refs (state_refs_of s); scheduler_action s = resume_cur_thread\<rbrakk>
     \<Longrightarrow> bound_sc_tcb_at ((=) (Some (cur_sc s))) (cur_thread s) s"
  by (clarsimp simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
     (drule (2) sym_ref_sc_tcb, clarsimp simp: pred_tcb_at_def obj_at_def)

lemma sc_is_round_robin_sa_update[simp]:
  "sc_is_round_robin t (s\<lparr>scheduler_action :=sa\<rparr>) = sc_is_round_robin t s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma sc_is_round_robin_rdq_update[simp]:
  "sc_is_round_robin t (s\<lparr>ready_queues :=rdq\<rparr>) = sc_is_round_robin t s"
  by (clarsimp simp: sc_is_round_robin_def)

(*   and sc_is_round_robin[wp]: "\<lambda>s. P (sc_is_round_robin p s)"
  and sc_is_round_robin_cur[wp]: "\<lambda>s. P (sc_is_round_robin (cur_sc s) s)" *)

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

lemma sc_is_round_robin_cur_thread_update[simp]:
  "sc_is_round_robin p (s\<lparr>cur_thread := param_a\<rparr>) = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma sc_is_round_robin_release_queue_update[simp]:
  "sc_is_round_robin p (s\<lparr>release_queue := param_a\<rparr>) = sc_is_round_robin p s"
  by (clarsimp simp: sc_is_round_robin_def)

lemma next_domain_sc_is_round_robin[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin p s)\<rbrace> next_domain \<lbrace>\<lambda>_. \<lambda>s. P (sc_is_round_robin p s)\<rbrace>"
  apply (clarsimp simp: sc_is_round_robin_def obj_at_def sc_at_pred_n_def)
  by wpsimp

lemma next_domain_sc_is_round_robin_cur[wp]:
  "\<lbrace>\<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace> next_domain \<lbrace>\<lambda>_. \<lambda>s. P (sc_is_round_robin (cur_sc s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_sc]; wpsimp)

crunches schedule_choose_new_thread, switch_to_thread, set_scheduler_action, tcb_sched_action
  for sc_at_period[wp]: "sc_at_period P p :: 'state_ext state \<Rightarrow> _"
    (wp: valid_sched_pred_heap_proj_lowers[where R=\<top>, simplified])

crunches switch_to_idle_thread
  for sc_is_round_robin[wp]: "\<lambda>s::'state_ext state. P (sc_is_round_robin p s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps Let_def)

crunches schedule_choose_new_thread
  for ready_or_release[wp]: "ready_or_release :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps Let_def cur_sc_chargeable_def)

lemma schedule_choose_new_thread_sc_at_period_cur[wp]:
  "\<lbrace>\<lambda>s :: ('state_ext state). sc_at_period P (cur_sc s) s\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
   by (rule hoare_lift_Pf[where f=cur_sc];
       wpsimp wp: valid_sched_pred_heap_proj_lowers[where R=\<top>, simplified])

lemma switch_to_thread_sc_at_period_cur[wp]:
  "\<lbrace>\<lambda>s::('state_ext state). sc_at_period P (cur_sc s) s\<rbrace> switch_to_thread t \<lbrace>\<lambda>_ s. sc_at_period P (cur_sc s) s\<rbrace>"
   by (rule hoare_lift_Pf[where f=cur_sc];
       wpsimp wp: valid_sched_pred_heap_proj_lowers[where R=\<top>, simplified])

(* FIXME move *)
lemma cur_tcb_get_tcb: "cur_tcb s \<Longrightarrow> \<exists>tcb. get_tcb (cur_thread s) s = Some tcb"
  by (clarsimp simp: cur_tcb_def obj_at_def is_tcb get_tcb_rev)

lemma not_schedulable_in_release_q_case:
  "\<lbrakk>\<not> is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s;
    ct_active s; active_sc_tcb_at (cur_thread s) s\<rbrakk>
       \<Longrightarrow> in_release_q (cur_thread s) s"
  by (clarsimp simp: is_schedulable_bool_def2 ct_in_state_def tcb_at_kh_simps runnable_eq_active)

lemma schedule_valid_sched_helper:
  "\<lbrace> valid_sched and invs and ct_active and ready_or_release
     and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)
     and (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> (\<not> budget_ready (cur_thread s) s))
     and (\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s)
     and (\<lambda>s. budget_sufficient (cur_thread s) s) and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
     and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s)
     and (\<lambda>s. cur_sc_budget_sufficient s) and cur_sc_chargeable\<rbrace>
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
  \<lbrace>\<lambda>_. valid_sched :: ('state_ext state) \<Rightarrow> _\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (simp, rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac action)
  apply (case_tac action; clarsimp)
    (* resume_cur_thread *)
    apply (wpsimp wp: sc_and_timer_valid_sched)
    apply (clarsimp simp: invs_def is_schedulable_bool_def get_tcb_def cur_tcb_def obj_at_def is_tcb_def
cur_sc_tcb_def sc_tcb_sc_at_def is_sc_obj_def
                   split: option.splits
                   dest!: get_tcb_SomeD)
    apply ((*rename_tac ko sc n;*) case_tac ko; clarsimp)
    apply (clarsimp simp: not_in_release_q_def)(*
     apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_release_q_def)
    apply (intro conjI impI; clarsimp simp: not_in_release_q_def)
    apply (clarsimp simp: valid_release_q_def valid_sched_def)
    apply (drule_tac x="idle_thread s" in bspec, simp, clarsimp)
    apply (drule (1) st_tcb_at_idle_thread, clarsimp)
    (* switch_thread *)
   apply (rename_tac candidate)
   apply (case_tac ct_released; clarsimp)
    (* ct is schedulable *)
    apply (wp del: hoare_when_wp
              add: schedule_choose_new_thread_valid_sched
                   schedule_choose_new_thread_ct_not_in_release_q
                   schedule_choose_new_thread_ct_not_queued
                   sc_and_timer_valid_sched)
               apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
                ready_or_release s \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
               apply wpsimp+
              apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and>
                                       scheduler_action s = choose_new_thread \<and> ct_in_q s \<and>
                                       simple_sched_action s \<and>
                                       (valid_idle and valid_ready_qs and valid_release_q) s \<and>
                ready_or_release s \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
                                       valid_machine_time s \<and> invs s" in hoare_strengthen_post[rotated])
               apply clarsimp
              apply (wpsimp wp: hoare_vcg_conj_lift)
               apply (rule set_scheduler_action_valid_blocked_const)
              apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
             apply (rule_tac Q="\<lambda>_ s. scheduler_action s = switch_thread candidate
                    \<and> in_ready_q candidate s \<and> ct_in_q s
                    \<and> valid_sched s \<and> invs s
                    \<and> cur_sc_in_release_q_imp_zero_consumed s
                    \<and> ready_or_release s
                    \<and> \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s
                    \<and> cur_sc_chargeable s \<and> valid_machine_time s
                    \<and> (\<not> sc_is_round_robin (cur_sc s) s)" in hoare_strengthen_post)
              apply (wpsimp wp: tcb_sched_enqueue_ct_in_q
                                enqueue_thread_queued[simplified in_ready_q_def[symmetric], simplified])
             apply (clarsimp simp: valid_sched_def)
            apply (wp schedule_choose_new_thread_valid_sched
                      schedule_choose_new_thread_ct_not_in_release_q
                      schedule_choose_new_thread_ct_not_queued)+
               apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
                ready_or_release s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and> cur_sc_chargeable s \<and>
 valid_machine_time s"
                       in hoare_strengthen_post[rotated], simp)
               apply wpsimp+
              apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and> scheduler_action s = choose_new_thread \<and>
                                        ct_in_q s \<and> simple_sched_action s \<and>
                                        (valid_idle and valid_ready_qs and valid_release_q) s \<and>
                                        cur_sc_in_release_q_imp_zero_consumed s \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
                ready_or_release s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and> cur_sc_chargeable s \<and>
                                        valid_machine_time s \<and> invs s"
                               in hoare_strengthen_post[rotated])
               apply (clarsimp simp: invs_def)
              apply (wpsimp wp: set_scheduler_action_obvious set_scheduler_action_valid_blocked_const)+
             apply (wpsimp wp: tcb_sched_append_valid_blocked_except_set_const)
             apply (rule_tac Q="\<lambda>_ s. scheduler_action s = switch_thread candidate \<and>
                                      in_ready_q candidate s \<and> ct_in_q s \<and>
                                      valid_sched s \<and> invs s \<and> cur_sc_in_release_q_imp_zero_consumed s \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
                ready_or_release s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and> cur_sc_chargeable s \<and>
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
             apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
                ready_or_release s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and> cur_sc_chargeable s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
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



apply (clarsimp simp: is_schedulable_bool_def valid_sched_def not_cur_thread_def
 valid_sched_action_def weak_valid_sched_action_def switch_in_cur_domain_def not_in_release_q_def
split: option.splits dest!: get_tcb_SomeD)
apply (intro conjI; (clarsimp simp: obj_at_def pred_tcb_at_def; fail)?)
apply (clarsimp simp: cur_sc_offset_ready_def)


apply (case_tac "sc_not_in_release_q (cur_sc s) s")
apply clarsimp

    apply (clarsimp simp: not_cur_thread_def valid_sched_def is_schedulable_bool_def simple_sched_action_def
                          cur_tcb_def active_sc_tcb_at_defs is_tcb get_tcb_rev not_in_release_q_def
                          valid_sched_action_def weak_valid_sched_action_def switch_in_cur_domain_def
                   split: option.splits)
apply (clarsimp cong: conj_cong imp_cong simp: valid_sched_def cur_sc_tcb_def dest!: invs_cur_sc_tcb)
apply (drule_tac x=tp in spec, clarsimp dest!: not_not_in_release_q_simp')
    apply (clarsimp simp: not_cur_thread_def valid_sched_def is_schedulable_bool_def simple_sched_action_def
                          cur_tcb_def active_sc_tcb_at_defs is_tcb get_tcb_rev not_in_release_q_def
                          valid_sched_action_def weak_valid_sched_action_def switch_in_cur_domain_def
                   split: option.splits)
apply (clarsimp simp: cur_sc_offset_ready_def is_refill_ready_def obj_at_def
sc_tcb_sc_at_def cur_sc_offset_sufficient_def
 split: option.splits kernel_object.splits)


apply (rule conjI; clarsimp?)

apply (clarsimp simp: is_refill_ready_def obj_at_def cur_sc_offset_ready_def
is_refill_sufficient_def sufficient_refills_defs cur_sc_offset_sufficient_def
cur_sc_budget_sufficient_def MIN_BUDGET_nonzero
  split: option.splits kernel_object.splits if_split_asm)


    (* ct is not schedulable *)
   apply (wp del: hoare_when_wp
             add: schedule_choose_new_thread_valid_sched
                  schedule_choose_new_thread_ct_not_in_release_q
                  schedule_choose_new_thread_ct_not_queued
                  sc_and_timer_valid_sched)
             apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               (ct_not_in_release_q s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s) \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
             apply (wpsimp wp: testing)+
            apply (rule_tac Q="\<lambda>rv s. valid_blocked s \<and>
                                      scheduler_action s = choose_new_thread \<and> ct_in_q s \<and>
                                      simple_sched_action s \<and>
                                      (valid_idle and valid_ready_qs and valid_release_q) s \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               (ct_not_in_release_q s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s) \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and> valid_machine_time s \<and> invs s"
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
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               (ct_not_in_release_q s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s) \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s"
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
           apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               (ct_not_in_release_q s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s) \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
           apply wpsimp+
apply (rule hoare_vcg_conj_lift)
apply (rule hoare_drop_imp)
           apply wpsimp+
          apply (wpsimp wp: guarded_switch_to_lift switch_to_thread_valid_sched
                            set_scheduler_action_rct_valid_sched_ct
                            stt_activatable[simplified ct_in_state_def]
                            hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                            switch_to_thread_sched_act_is_cur
                            switch_to_thread_ct_not_in_release_q switch_to_thread_invs)+
      (* discard result of fastfail calculation *)
       apply (wpsimp wp: hoare_drop_imp)+
apply (drule (2) not_schedulable_in_release_q_case, clarsimp)

apply (clarsimp simp: in_release_q_def not_in_release_q_def)

   apply (clarsimp simp: not_cur_thread_def valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                         switch_in_cur_domain_def active_sc_tcb_at_defs valid_blocked_def
                         ct_in_q_def in_release_queue_def not_in_release_q_def cur_tcb_def
                         is_tcb get_tcb_rev is_schedulable_bool_def valid_blocked_except_def
                  split: option.splits)
    (* choose new thread *)
  apply (case_tac ct_released; clarsimp)
   apply (wpsimp wp: schedule_choose_new_thread_valid_sched
                     schedule_choose_new_thread_ct_not_in_release_q
                     schedule_choose_new_thread_ct_not_queued
                     sc_and_timer_valid_sched)
     apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
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
   apply (rule_tac Q="\<lambda>rv s. (valid_state s \<and> cur_tcb s) \<and>
              cur_sc_in_release_q_imp_zero_consumed s \<and>
               \<not> sc_is_round_robin (cur_sc s) s \<and>
               cur_sc_offset_ready (consumed_time s) s \<and>
               cur_sc_offset_sufficient (consumed_time s) s \<and>
               cur_sc_budget_sufficient s \<and>
 valid_machine_time s" in hoare_strengthen_post[rotated], simp)
   apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except_set_const)+
  by (clarsimp simp: valid_sched_def ct_in_q_def not_in_release_q_def in_release_queue_def
                     is_schedulable_bool_def active_sc_tcb_at_defs cur_tcb_def is_tcb get_tcb_rev
              split: option.splits) *)
  sorry (* schedule_valid_sched_helper *)

crunches awaken
  for ct_in_state[wp]: "ct_in_state P"
    (wp: crunch_wps hoare_vcg_disj_lift simp: crunch_simps pred_disj_def)

lemma awaken_valid_sched_misc[wp]:
  "awaken \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s)
                 (cur_thread s) (idle_thread s) (last_machine_time_of s) (kheap s) \<rbrace>"
  by (wpsimp simp: awaken_def wp: mapM_x_wp_inv hoare_drop_imp)

crunches awaken
  for sc_at_period[wp]: "sc_at_period P p :: 'state_ext state \<Rightarrow> _"
  and sc_at_period_cur[wp]: "\<lambda>s. sc_at_period P (cur_sc s) s"
    (simp: crunch_simps wp: crunch_wps)

(* FIXME move *)
lemma valid_release_q_sorted: "valid_release_q s \<Longrightarrow> sorted_release_q s"
  by (clarsimp simp: valid_release_q_def)

(* FIXME: move up to replace sorted_wrt_img_ord_eq_lift *)
lemma sorted_wrt_cong:
  assumes "xs=ys"
  and "\<And>x y. \<lbrakk>x \<in> set ys; y \<in> set ys\<rbrakk> \<Longrightarrow> cmp x y = cmp' x y"
  shows "sorted_wrt cmp xs = sorted_wrt cmp' ys"
  using assms by (induct xs; metis sorted_wrt_mono_rel)

lemma in_release_q_has_ready_time:
  fixes s :: "'z state"
  assumes "valid_release_q s"
  assumes "t \<in> set (release_queue s)"
  shows "\<exists>rt. tcb_ready_times_of s t = Some rt"
  using assms valid_release_q_active_sc[OF assms]
  by (auto simp: tcb_ready_times_defs map_project_simps opt_map_simps map_join_simps vs_all_heap_simps)

lemma in_release_q_opt_ord_conv:
  fixes s :: "'z state"
  assumes vrq: "valid_release_q s"
  assumes t: "t \<in> set (release_queue s)"
  assumes t': "t' \<in> set (release_queue s)"
  shows "opt_ord (tcb_ready_times_of s t) (tcb_ready_times_of s t') \<longleftrightarrow> tcb_ready_time t s \<le> tcb_ready_time t' s"
  using in_release_q_has_ready_time[OF vrq t] in_release_q_has_ready_time[OF vrq t']
  by auto

lemma budget_ready_def2:
  "active_sc_tcb_at t s
   \<Longrightarrow> budget_ready t s \<longleftrightarrow> tcb_ready_time t s \<le> cur_time s + kernelWCET_ticks"
  by (auto simp: vs_all_heap_simps refill_ready_def tcb_ready_times_defs
                    opt_map_def map_project_def map_join_def pred_map_simps
                    tcb_scps_of_tcbs_def tcbs_of_kh_def
                    sc_refill_cfgs_of_scs_def scs_of_kh_def
             split: option.split)

lemma dropWhile_release_queue:
 "\<lbrakk> valid_release_q s; active_sc_valid_refills s;
   t \<in> set (dropWhile (\<lambda>t. the (fun_of_m (get_tcb_refill_ready t) s)) (release_queue s))\<rbrakk>
   \<Longrightarrow> \<not>budget_ready t s"
  apply (frule set_dropWhileD)
  apply (frule (1) valid_release_q_active_sc)
  apply (frule valid_release_q_sorted)
  apply (prop_tac
      "(dropWhile (\<lambda>t. the (fun_of_m (get_tcb_refill_ready t) s))
                (release_queue s)) =
           (dropWhile (\<lambda>t. tcb_ready_time t s \<le> (cur_time s) + kernelWCET_ticks)
                (release_queue s))")

   apply (rule dropWhile_cong, clarsimp)
   apply (subst get_tcb_refill_ready_simp2)
   apply (erule (2) active_sc_tcb_at_budget_sufficient[OF valid_release_q_active_sc])
  apply simp+
  apply (thin_tac "(dropWhile _ _)=  _")
  apply (frule sorted_wrt_dropWhile_mono[rotated, where f="\<lambda>t. tcb_ready_time t s"])
    apply (fastforce)
  apply (fastforce simp: sorted_release_q_def img_ord_def in_release_q_opt_ord_conv
                elim!: sorted_wrt_cong[THEN iffD2, rotated -1])
  apply (simp add: budget_ready_def2)
  done

lemma awaken_cur_thread_in_rlq:
  "\<lbrace>active_sc_valid_refills
    and cur_tcb
    and valid_release_q \<rbrace>
      awaken
   \<lbrace>\<lambda>rv s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: awaken_def)
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift simp: thread_get_def)
  apply (simp add: dropWhile_eq_drop[symmetric] in_release_q_def in_queue_2_def)
  apply (frule (2) dropWhile_release_queue)
  by simp

lemma awaken_cur_thread_not_in_rlq:
  "\<lbrace>(\<lambda>s. not_in_release_q (cur_thread s) s \<longrightarrow> budget_ready (cur_thread s) s)
    and cur_tcb
    and valid_release_q\<rbrace>
      awaken
    \<lbrace>\<lambda>rv s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: awaken_def not_in_release_q_def)
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift hoare_vcg_conj_lift simp: thread_get_def)
  apply (clarsimp simp: dropWhile_eq_drop[symmetric])
  apply (drule (1) dropWhile_dropped_P[rotated])
  apply (frule (1) valid_release_q_active_sc)
  apply (clarsimp simp: fun_of_m_get_tcb_refill_budget_ready vs_all_heap_simps)
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
  apply (wpsimp wp: tcb_sched_enqueue_not_queued thread_get_wp get_tcb_obj_ref_wp | wps)+
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemma possible_switch_to_scheduler_act_sane'':
  "\<lbrace>scheduler_act_sane and (\<lambda>s. cur_thread s \<noteq> thread)\<rbrace>
     possible_switch_to thread \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  by (wpsimp wp: tcb_sched_action_scheduler_action hoare_drop_imp simp: set_scheduler_action_def)
     (clarsimp simp: scheduler_act_sane_def)

lemma awaken_ct_not_queued_helper:
  "\<lbrace>ct_not_queued and (\<lambda>s. cur_thread s \<notin> set queue) and scheduler_act_sane\<rbrace>
     mapM_x (\<lambda>t. do consumed <- gets consumed_time;
                       tcb <- gets_the (get_tcb t);
                       scp <- assert_opt (tcb_sched_context tcb);
                       sufficient <- get_sc_refill_sufficient scp consumed;
                       y <- assert sufficient;
                       y <- possible_switch_to t;
                       modify (reprogram_timer_update (\<lambda>_. True))
                    od) queue
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (induction queue, wpsimp simp: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
  by (wpsimp wp: possible_switch_to_ct_not_queued possible_switch_to_scheduler_act_sane'' hoare_drop_imp)

lemma awaken_ct_not_queued:
  "\<lbrace>ct_not_queued
    and scheduler_act_sane
    and valid_release_q
    and (\<lambda>s. (in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s))\<rbrace>
   awaken
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: awaken_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_ct_not_queued_helper simp: thread_get_def)
  apply (drule set_takeWhileD)
  apply (clarsimp simp: in_queue_2_def valid_release_q_def)
  apply (subst (asm) fun_of_m_get_tcb_refill_budget_ready)
  apply (clarsimp simp: vs_all_heap_simps, fastforce)
  apply (clarsimp)
  done

(* unused? *)
crunches awaken
  for sc_is_round_robin[wp]: "\<lambda>s::det_state. P (sc_is_round_robin p s)"
  and sc_is_round_robin_cur[wp]: "\<lambda>s::det_state. P (sc_is_round_robin (cur_sc s) s)"
    (wp: crunch_wps simp: crunch_simps)

lemma awaken_ct_cur_sc_in_release_q_imp_zero_consumed[wp]:
  "awaken \<lbrace>cur_sc_in_release_q_imp_zero_consumed ::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: awaken_def wp: mapM_x_wp' hoare_drop_imp)
  apply (drule_tac x=t in spec, clarsimp simp: not_in_release_q_def)
  apply (clarsimp simp: in_queue_2_def dropWhile_eq_drop[symmetric] pred_tcb_at_def obj_at_def)
  apply (drule set_dropWhileD, clarsimp)
  done

lemma awaken_ready_or_release_helper:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. tcb_at t s) and ready_or_release and K (distinct queue)\<rbrace>
       mapM_x (\<lambda>t. do consumed <- gets consumed_time;
                       sc_opt <- thread_get tcb_sched_context t;
                       scp <- assert_opt sc_opt;
                       sufficient <- get_sc_refill_sufficient scp consumed;
                       y <- assert sufficient;
                       y <- possible_switch_to t;
                       modify (reprogram_timer_update (\<lambda>_. True))
                    od) queue
   \<lbrace>\<lambda>_. ready_or_release :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (rule hoare_gen_asm, rule ball_mapM_x_scheme, (wpsimp wp: hoare_drop_imp)+)

lemma awaken_ready_or_release[wp]:
  "\<lbrace>\<lambda>s. ready_or_release s \<and> valid_release_q s\<rbrace>
   awaken
   \<lbrace>\<lambda>_. ready_or_release :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding awaken_def
  apply (wpsimp simp: awaken_def wp: awaken_ready_or_release_helper)
  apply (clarsimp simp: ready_or_release_2_def valid_release_q_def dropWhile_eq_drop[symmetric])
  apply (intro conjI; clarsimp?)
   apply (drule_tac x=t in bspec, clarsimp dest!: set_takeWhileD)
   apply (clarsimp simp: vs_all_heap_simps tcb_at_def get_tcb_def)
  by (drule_tac x=t in spec, clarsimp dest!: set_dropWhileD simp: in_queue_2_def)

lemma awaken_it_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. not_in_release_q (idle_thread s) s\<rbrace>
     awaken \<lbrace>\<lambda>_. \<lambda>s. not_in_release_q (idle_thread s) s\<rbrace>"
  apply (wpsimp simp: awaken_def wp: mapM_x_wp' hoare_drop_imp)
  apply (clarsimp simp: not_in_release_q_def in_queue_2_def dropWhile_eq_drop[symmetric])
  by (drule set_dropWhileD, clarsimp)

lemma takeWhile_release_queue:
  "\<lbrakk> \<exists>scp. bound_sc_tcb_at (\<lambda>x. x = (Some scp)) t s \<and> sc_refills_sc_at (\<lambda>x. x\<noteq>[]) scp s;
     t \<in> set (takeWhile (\<lambda>t. the (fun_of_m (get_tcb_refill_ready t) s)) (release_queue s))\<rbrakk>
     \<Longrightarrow> budget_ready t s"
  apply (drule set_takeWhileD)
  by (clarsimp simp: fun_of_m_get_tcb_refill_budget_ready vs_all_heap_simps
                     obj_at_kh_kheap_simps)

(* FIXME move *)
lemma notdropWhile_takeWhile:
  "t \<in> set q
   \<Longrightarrow> t \<notin> set (dropWhile P q)
   \<Longrightarrow> t \<in> set (takeWhile P q)"
  apply (subst (asm) takeWhile_dropWhile_id[symmetric])
  apply (simp only: set_append)
  by fastforce

lemma awaken_ct_nrq_wbr:
  "\<lbrace>(\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s) and
    (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s) and
    valid_release_q and
    (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> budget_sufficient (cur_thread s) s)\<rbrace>
    awaken
   \<lbrace>\<lambda>_ s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s\<rbrace>"
  unfolding awaken_def
  apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift' simp: thread_get_def)
  apply (clarsimp simp: dropWhile_eq_drop[symmetric] in_queue_2_def)
  apply (drule (1) notdropWhile_takeWhile[rotated])
  apply (drule set_takeWhileD, clarsimp)
  by (clarsimp simp: fun_of_m_get_tcb_refill_budget_ready vs_all_heap_simps
                     obj_at_kh_kheap_simps)

(* ct_released \<longrightarrow> ready & sufficient
lemma schedule_valid_sched':
  "\<lbrace> ct_active and
    (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
    (\<lambda>s. budget_sufficient (cur_thread s) s) and
   (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and (\<lambda>s.  \<not> sc_is_round_robin (cur_sc s) s)
     and (\<lambda>s. if  ct_not_in_release_q s
              then budget_ready (cur_thread s) s \<and> budget_sufficient (cur_thread s) s
              else \<not> budget_ready (cur_thread s) s)
     and valid_sched and scheduler_act_sane and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s.  \<not> sc_is_round_robin (cur_sc s) s)
     and (\<lambda>s. ct_not_in_release_q s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
     and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s)
     and (\<lambda>s. cur_sc_budget_sufficient s)
     and invs\<rbrace>
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
*)

lemma awaken_in_release_q:
  "\<lbrace>in_release_q t
    and valid_release_q
    and (\<lambda>s. bound_sc_tcb_at (\<lambda>scpo. scpo \<noteq> None \<longrightarrow> (\<not>is_refill_ready (the scpo) s)) t s)\<rbrace>
   awaken
   \<lbrace>\<lambda>rv s. in_release_q t s\<rbrace>"
  supply takeWhile_dropWhile_id [simp del]
  apply (wpsimp simp: awaken_def wp: mapM_x_wp' hoare_drop_imp)
  apply (clarsimp simp: not_in_release_q_def in_queue_2_def dropWhile_eq_drop[symmetric])
  apply (subst (asm) takeWhile_dropWhile_id[symmetric])
  apply clarsimp
  apply (erule disjE)
   defer
   apply (assumption)
  apply (drule set_takeWhileD, clarsimp)
  apply (subst (asm) fun_of_m_get_tcb_refill_budget_ready)
   apply (clarsimp simp: valid_release_q_def)
   apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps, fastforce)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps)
  done

lemma awaken_cur_sc_not_in_rlq_offset_ready:
  "\<lbrace>(\<lambda>s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
    and valid_release_q
    and (\<lambda>s. cur_sc_offset_ready 0 s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   awaken
   \<lbrace>\<lambda>rv s. sc_not_in_release_q (cur_sc s) s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s\<rbrace>"
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift awaken_in_release_q)
  apply (drule_tac x=t in spec, clarsimp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def vs_all_heap_simps cur_sc_offset_ready_def refill_ready_def)
  using le_trans unat_le_mono unat_plus_gt by blast

lemma schedule_valid_sched:
  "\<lbrace> valid_sched
     and invs
     and ct_active and ready_or_release and
    (\<lambda>s. ct_not_in_release_q s \<longrightarrow> budget_ready (cur_thread s) s) and
    (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
    (\<lambda>s. in_release_q (cur_thread s) s \<longrightarrow> \<not> budget_ready (cur_thread s) s) and
    (\<lambda>s. budget_sufficient (cur_thread s) s) and
    (\<lambda>s. is_schedulable_bool (cur_thread s) (in_release_q (cur_thread s) s) s \<longrightarrow>
              budget_ready (cur_thread s) s \<and> budget_sufficient (cur_thread s) s) and
    \<comment> \<open>(\<lambda>s. cur_thread s \<notin> set (release_queue s) \<longrightarrow> budget_ready (cur_thread s) s) and\<close>
   (\<lambda>s. active_sc_tcb_at (cur_thread s) s)
     and scheduler_act_sane and ct_not_queued
     and cur_sc_in_release_q_imp_zero_consumed
     and (\<lambda>s.  \<not> sc_is_round_robin (cur_sc s) s)
     and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
     and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s)
     and (\<lambda>s. cur_sc_budget_sufficient s) and cur_sc_chargeable\<rbrace>
   schedule
  \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding schedule_def
   apply (wpsimp wp: schedule_valid_sched_helper)
   apply (wpsimp wp: awaken_valid_sched
                     awaken_ready_or_release
                     awaken_cur_thread_in_rlq
                     awaken_cur_thread_not_in_rlq
                     awaken_ct_not_queued
                     awaken_cur_sc_not_in_rlq_offset_ready)
   apply (clarsimp simp: valid_sched_def in_release_q_def)
  by (intro conjI; clarsimp)

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
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding restart_def
  apply (wpsimp wp: test_possible_switch_to_valid_sched wp_del: maybeM_wp)
       apply (rule_tac Q="\<lambda>r s. valid_sched_except_blocked s
                                \<and> valid_blocked_except_set {thread} s
                                \<and> thread \<noteq> idle_thread s
                                \<and> (st_tcb_at runnable thread s \<and> active_sc_tcb_at thread s \<and>
                                   not_in_release_q thread s \<longrightarrow>
                                   budget_ready thread s \<and> budget_sufficient thread s)"
                       in hoare_strengthen_post[rotated])
        apply (intro allI conjI;
               intro impI;
               clarsimp simp: valid_sched_def tcb_at_kh_simps dest!: is_schedulable_opt_Some)
        apply (clarsimp elim!: valid_blocked_divided_threadE
                        simp: valid_blocked_thread_def runnable_eq_active)
       apply (wpsimp wp: sched_context_resume_valid_sched_except_blocked
                         sched_context_resume_valid_blocked_except_set
                         sched_context_resume_cond_budget_ready_sufficient)
      apply (rule_tac Q="\<lambda>r. (valid_sched_except_blocked and
                             valid_blocked_except_set {thread}) and
                             scheduler_act_not thread and
                             not_queued thread and
                             (\<lambda>s. thread \<noteq> idle_thread s) and
                             (\<lambda>s. \<forall>sc_ptr. sc_opt = (Some sc_ptr)
                                           \<longrightarrow> sc_tcb_sc_at ((=) (Some thread)) sc_ptr s) and
                             bound_sc_tcb_at (\<lambda>a. a = sc_opt) thread"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise heap_refs_retract_at_def vs_all_heap_simps)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift set_thread_state_break_valid_sched)
     apply clarsimp
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift cancel_ipc_valid_sched)
    apply (wpsimp simp: get_tcb_obj_ref_def  wp: thread_get_wp )
   apply (wpsimp wp: gts_wp )
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac x=tcb in exI; clarsimp)
  apply (intro conjI; clarsimp)
   apply (subgoal_tac "st_tcb_at runnable thread s")
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (drule valid_ready_qs_in_ready_qD[rotated], simp add: valid_sched_def)
   apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def
                         pred_tcb_at_def obj_at_def)
  apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[where t=thread, symmetric];
         simp?;
         fastforce simp: pred_tcb_at_def obj_at_def)
  done

end

lemma bind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> bind_notification param_a param_b \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: bind_notification_def update_sk_obj_ref_def)
  apply (wpsimp simp: set_object_def set_simple_ko_def
          wp: get_simple_ko_wp hoare_drop_imp)
  done

lemma suspend_it_det_ext[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> suspend param_a \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: suspend_def wp: hoare_drop_imps)


context DetSchedSchedule_AI_det_ext begin

lemma invoke_tcb_valid_sched:
  "\<lbrace>invs
    and valid_sched and ct_active and ct_released and ct_not_in_release_q
    and simple_sched_action
    and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s)
    and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (cases ti, simp_all only:)
         \<comment> \<open>WriteRegisters\<close>
         apply (wpsimp wp: restart_valid_sched reschedule_valid_sched_const hoare_vcg_if_lift2
                           hoare_vcg_imp_lift' arch_post_modify_registers.valid_sched_pred)
               apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated], fastforce)
               apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' )+
              apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated], fastforce)
              apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' )+
         apply (subgoal_tac "x11 \<noteq> idle_thread s", clarsimp)
          apply (clarsimp simp: invs_valid_objs invs_valid_global_refs idle_no_ex_cap)
         \<comment> \<open>ReadRegisters\<close>
         apply (wpsimp wp: suspend_valid_sched;
               clarsimp simp: invs_valid_objs invs_valid_global_refs split: if_splits)
         \<comment> \<open>CopyRegisters\<close>
       apply (wpsimp wp: reschedule_valid_sched_const mapM_x_wp, assumption)
          apply (wpsimp wp: mapM_x_wp, assumption)
         apply (wpsimp wp: restart_valid_sched hoare_vcg_if_lift2 hoare_vcg_imp_lift')
        apply (wpsimp wp: suspend_valid_sched hoare_vcg_if_lift2 hoare_vcg_imp_lift')
          apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated], fastforce)
          apply (wpsimp wp: suspend_invs suspend_valid_sched hoare_vcg_if_lift2 hoare_vcg_imp_lift')+
          apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated], fastforce)
          apply (wpsimp wp: suspend_invs suspend_valid_sched hoare_vcg_if_lift2 hoare_vcg_imp_lift')+
         apply (rule_tac Q="\<lambda>rv s. invs s \<and> simple_sched_action s" in hoare_strengthen_post[rotated], fastforce)
         apply (wpsimp wp: suspend_invs suspend_valid_sched hoare_vcg_if_lift2 hoare_vcg_imp_lift')+
       apply (subgoal_tac "x31 \<noteq> idle_thread s \<and> x32 \<noteq> idle_thread s")
        apply (clarsimp simp: invs_def valid_pspace_def valid_state_def valid_idle_def split: if_splits)
        apply (fastforce simp: invs_def valid_state_def valid_idle_def dest!: idle_no_ex_cap)
         \<comment> \<open>ThreadControl\<close>
       apply (wp tcc_valid_sched)
       apply (rename_tac sc_opt_opt s, case_tac sc_opt_opt; simp)
      apply (wp tcs_valid_sched)
      apply (rename_tac sc_opt_opt s, case_tac sc_opt_opt; simp)
     apply (rename_tac sc_opt, case_tac sc_opt; simp)
        \<comment> \<open>Suspend\<close>
     apply (wpsimp wp: suspend_valid_sched ;
            clarsimp simp: invs_valid_objs invs_valid_global_refs)
         \<comment> \<open>Resume\<close>
    apply (wpsimp wp: mapM_x_wp suspend_valid_sched restart_valid_sched;
           intro conjI;
           clarsimp simp: invs_valid_objs invs_valid_global_refs idle_no_ex_cap)
         \<comment> \<open>NotificationControl\<close>
   apply (rename_tac option, case_tac option; wpsimp)
         \<comment> \<open>SetTLSBase\<close>
  apply (wpsimp wp: reschedule_valid_sched_const)
  done

end

crunch exst[wp]: set_mrs, as_user "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

lemmas gts_drop_imp = hoare_drop_imp[where f="get_thread_state p" for p]

crunch not_cur_thread[wp]: cap_insert, set_extra_badge "not_cur_thread t"
  (wp: hoare_drop_imps dxo_wp_weak)

lemma transfer_caps_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

crunch (in DetSchedSchedule_AI) not_cur_thread[wp] : do_ipc_transfer "not_cur_thread t:: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

lemma postpone_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q \<rbrace>
     postpone sc_ptr
   \<lbrace> \<lambda>_. ct_not_in_q\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp:get_sc_obj_ref_wp)

lemma sched_context_resume_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q \<rbrace>
   sched_context_resume sc_ptr
   \<lbrace> \<lambda>_. ct_not_in_q\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: thread_get_wp is_schedulable_wp)
  by (fastforce simp: obj_at_def is_schedulable_bool_def is_tcb
               split: option.splits dest!: get_tcb_SomeD)

lemma maybe_donate_sc_ct_not_in_q[wp]:
  "maybe_donate_sc tcb_ptr ntfnptr \<lbrace>ct_not_in_q\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

crunches sched_context_donate
  for machine_state[wp]: "(\<lambda>s. P (machine_state s))"
  (wp: crunch_wps)

lemma maybe_donate_sc_valid_ready_qs:
  "\<lbrace>valid_ready_qs and scheduler_act_not tcb_ptr and valid_machine_time and active_sc_valid_refills\<rbrace>
   maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
  apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise)
  by (wpsimp wp: get_sc_obj_ref_wp)

lemma maybe_donate_sc_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> valid_machine_time s \<and> active_sc_valid_refills s
        \<and> (\<forall>scp. ntfn_at_ppred ntfn_sc ((=) (Some scp)) ntfnptr s
                 \<longrightarrow> sched_context_donate_ipc_queues_precond tcb_ptr scp s)\<rbrace>
   maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_when_cases; clarsimp)
  apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
  apply (wpsimp wp: sched_context_donate_released_sc_released_ipc_queues
                    hoare_vcg_if_lift2 maybeM_wp valid_machine_time_lift
              simp: get_sc_obj_ref_def obj_at_def)
  apply (subgoal_tac "ntfn_at_ppred ntfn_sc ((=) (Some xa)) ntfnptr s", fastforce)
  apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
  done

lemma maybe_donate_sc_released_ipc_queues':
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> valid_machine_time s \<and> active_sc_valid_refills s
        \<and> \<not>ipc_queued_thread tcbptr s\<rbrace>
     maybe_donate_sc tcbptr ntfnptr
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  by (wpsimp wp: maybe_donate_sc_released_ipc_queues simp: pred_map_ipc_queued_thread_state_iff)

lemma refill_unblock_check_ko_at_SchedContext:
  "\<lbrace>\<lambda>s. P (sc_tcb_sc_at ((=) (Some ya)) scp s)\<rbrace>
    refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. P (sc_tcb_sc_at ((=) (Some ya)) scp s)\<rbrace>"
   unfolding refill_unblock_check_def
  by (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
     (clarsimp simp: sc_at_pred_n_def obj_at_def)

lemma maybe_donate_sc_valid_release_q_helper:
  "\<lbrace>not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr and sc_tcb_sc_at ((=) None) scp\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) scp s \<longrightarrow>
               st_tcb_at runnable x s \<and> not_in_release_q x s \<and> bound_sc_tcb_at ((=) (Some scp)) x s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def
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

lemma sched_context_donate_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>y s. not_in_release_q t s\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp simp: set_tcb_obj_ref_def
                  wp: set_object_wp update_sched_context_wp hoare_drop_imp
                      tcb_release_remove_not_in_release_q' get_sc_obj_ref_wp)

(* FIXME: rename *)
lemma sched_context_donate_wp:
  "\<lbrace>\<top>\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>y. sc_tcb_sc_at ((=) (Some tcb_ptr)) scp and bound_sc_tcb_at ((=) (Some scp)) tcb_ptr\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: ssc_bound_tcb_at' sc_tcb_update_sc_tcb_sc_at)


lemma maybe_donate_sc_valid_release_q_helper':
  "\<lbrace>valid_release_q and bound_sc_tcb_at ((=) None) tcb_ptr
       and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>t\<in>set (release_queue s). bound_sc_tcb_at (\<lambda>p. p \<noteq> Some scp) t s\<rbrace>"
  apply (rule_tac Q="valid_release_q and not_in_release_q tcb_ptr and valid_objs
                      and (\<lambda>s. sym_refs (state_refs_of s)) and bound_sc_tcb_at ((=) None) tcb_ptr"
           in hoare_weaken_pre[rotated])
   apply (clarsimp dest!: valid_release_q_no_sc_not_in_release_q[rotated] simp: tcb_at_kh_simps(3))
  apply (rule_tac Q="\<lambda>_ . sc_tcb_sc_at ((=) (Some tcb_ptr)) scp
                    and bound_sc_tcb_at ((=) (Some scp)) tcb_ptr and not_in_release_q tcb_ptr
                    and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs and valid_release_q"
           in hoare_strengthen_post)
   apply (wpsimp wp: sched_context_donate_wp sched_context_donate_not_in_release_q
      sched_context_donate_valid_release_q sched_context_donate_sym_refs)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_release_q_def)
  apply (drule_tac x=t in bspec, simp)
  apply (clarsimp simp: not_in_release_q_def sc_tcb_sc_at_def obj_at_def vs_all_heap_simps split: option.splits)
  apply (frule_tac tp=tcb_ptr and scp=ref' in sym_ref_tcb_sc, simp+)
  apply (drule_tac tp=t and scp=ref' in sym_ref_tcb_sc, simp+)
  done

lemma tcb_release_remove_sc_not_in_release_q[wp]:
  "\<lbrace>sc_not_in_release_q sc_ptr\<rbrace>
    tcb_release_remove tptr
   \<lbrace>\<lambda>rv. sc_not_in_release_q sc_ptr\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  by (clarsimp simp: pred_tcb_at_def obj_at_def tcb_sched_dequeue_def not_in_release_q_def in_queue_2_def)

lemma sched_context_donate_sc_not_in_release_q:
  "\<lbrace>sc_not_in_release_q sc_ptr and not_in_release_q tptr\<rbrace>
    sched_context_donate scp tptr
   \<lbrace>\<lambda>rv. sc_not_in_release_q sc_ptr\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  by (wpsimp wp: get_sc_obj_ref_wp hoare_vcg_imp_lift' tcb_release_remove_not_in_release_q')

lemma maybe_donate_sc_valid_release_q:
  "\<lbrace> valid_release_q and not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr
           and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_release_q \<rbrace>"
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
                      sched_context_donate_valid_release_q
                      sched_context_donate_sc_not_in_release_q)
    apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def tcb_at_kh_simps[symmetric])
    apply (drule (2) bound_sc_tcb_bound_sc_at)
     apply (fastforce simp: pred_tcb_at_def obj_at_def sc_tcb_sc_at_def)
    apply fastforce
  by (wpsimp wp: sched_context_donate_valid_release_q maybe_donate_sc_valid_release_q_helper')+

lemma maybe_donate_sc_valid_sched_action_helper:
  "\<lbrace>scheduler_act_not tcb_ptr and sc_tcb_sc_at ((=) None) scp\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) scp s \<longrightarrow> scheduler_act_not x s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
        apply (rule hoare_pre_cont)
       apply (wpsimp)+
   apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  done

lemma maybe_donate_sc_valid_sched_action:
  "\<lbrace> valid_sched_action and scheduler_act_not tcb_ptr and valid_machine_time and active_sc_valid_refills\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_sched_action \<rbrace>"
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

lemma maybe_donate_sc_ct_in_cur_domain:
  "\<lbrace> ct_in_cur_domain \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_in_cur_domain \<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma not_queued_refill_unblock_check:
  "\<lbrace>\<lambda>s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>rv s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_donate_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set {tcb_ptr} and sc_tcb_sc_at ((=) None) sc_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>y. valid_blocked_except_set {tcb_ptr}\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
        apply (rule hoare_pre_cont)
       apply (wpsimp)+
   apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply (safe)
   apply clarsimp
  apply (clarsimp simp: valid_blocked_except_set_2_def valid_blocked_thread_def
                 dest!: get_tcb_SomeD split: if_splits)
  apply (drule_tac x=t in spec)
  by (clarsimp simp: vs_all_heap_simps)

lemma not_queued_sched_context_donate:
  "\<lbrace>not_queued tcb_ptr and scheduler_act_not tcb_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  apply (wpsimp wp: get_sched_context_wp hoare_vcg_all_lift set_object_wp get_object_wp)
      apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
     apply (wpsimp wp: update_sched_context_wp)
    apply (rule_tac Q="\<lambda>r. not_queued tcb_ptr" in hoare_strengthen_post)
     prefer 2
     apply (clarsimp simp: not_queued_def sc_tcb_sc_at_def obj_at_def dest!: get_tcb_SomeD)
    apply (wpsimp wp: tcb_dequeue_not_queued_gen simp: get_sc_obj_ref_def)+
  done

lemma maybe_donate_sc_valid_blocked_except_set:
  "\<lbrace> valid_blocked_except_set {tcb_ptr} and not_queued tcb_ptr and scheduler_act_not tcb_ptr\<rbrace>
      maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_blocked_except_set {tcb_ptr} \<rbrace>"
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
            set_thread_state_valid_ready_qs
            set_thread_state_valid_sched_action
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
  apply (wpsimp wp: set_tcb_queue_wp simp: thread_get_def)
  apply (fastforce simp: not_queued_def obj_at_def in_queues_2_def dest!: get_tcb_SomeD)
  done

lemma restart_thread_if_no_fault_ipc_queued_thread_neq:
  "\<lbrace>\<lambda>s. pred_map P (tcb_sts_of s) t' \<and> t' \<noteq> t\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_ s. pred_map P (tcb_sts_of s) t'\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp wp: set_thread_state_pred_map_tcb_sts_of thread_get_wp')

lemma cancel_badged_sends_filterM_valid_sched:
   "\<lbrace>(\<lambda>s. \<forall>t\<in>set xs. blocked_on_send_tcb_at t s \<and> t \<noteq> idle_thread s)
     and valid_sched and K (distinct xs)\<rbrace>
    filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                    if blocking_ipc_badge st = badge
                    then do _ \<leftarrow> restart_thread_if_no_fault t;
                            return False
                    od
                    else return True
                 od) xs
    \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_gen_asm, rule ball_filterM_scheme[rotated 2], simp)
   apply (wpsimp wp: restart_thread_if_no_fault_ipc_queued_thread_neq hoare_drop_imp)
  apply (wpsimp wp: restart_thread_if_no_fault_valid_sched_not_runnable hoare_drop_imp)
  apply (intro conjI)
   apply (clarsimp simp: pred_map_simps is_blocked_thread_state_defs)
  apply (frule valid_sched_released_ipc_queues, clarsimp simp: released_ipc_queues_defs)
  apply (drule_tac x=t in spec)
  apply (clarsimp simp: vs_all_heap_simps is_timeout_fault_opt_def)
  done

lemma cancel_badged_sends_valid_sched:
  "\<lbrace>valid_objs and valid_sched and simple_sched_action
    and (\<lambda>s. sym_refs (state_refs_of s)) and valid_idle\<rbrace>
   cancel_badged_sends epptr badge
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp;
          wpsimp wp: cancel_badged_sends_filterM_valid_sched hoare_vcg_ball_lift
                     reschedule_valid_sched_const)
  apply (intro conjI, intro ballI)
   apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>payl. st = (BlockedOnSend epptr payl)) x s")
    apply (intro conjI)
     apply (clarsimp simp: tcb_at_kh_simps pred_map_def)
    apply (clarsimp, drule (1) st_tcb_at_idle_thread, simp)
   apply (subgoal_tac "tcb_at x s")
    apply (subgoal_tac "(epptr, TCBBlockedSend) \<in> state_refs_of s x")
     apply (clarsimp simp: state_refs_of_def refs_of_def tcb_at_def is_tcb get_refs_def
                           tcb_st_refs_of_def pred_tcb_at_def obj_at_def
                    dest!: get_tcb_SomeD split: option.splits thread_state.splits if_splits)
    apply (erule sym_refsE, clarsimp)
    apply (clarsimp simp: obj_at_def state_refs_of_def refs_of_def split: option.splits)
   apply (fastforce elim: ep_list_tcb_at')
  apply (fastforce elim: valid_objs_SendEP_distinct simp: obj_at_def)
  done

context DetSchedSchedule_AI_det_ext begin

lemma cap_revoke_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action and invs\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule validE_valid, rule cap_revoke_preservation)
    apply (wpsimp wp: preemption_point_inv')+
  done

lemma cap_revoke_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  by (wp cap_revoke_preservation preemption_point_inv' | fastforce)+

end

lemma thread_set_state_eq_ct_in_cur_domain:
  "\<lbrakk> \<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x \<rbrakk> \<Longrightarrow>
   \<lbrace>ct_in_cur_domain and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done
(*
lemma thread_set_state_eq_valid_blocked:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_blocked and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp: dest!: get_tcb_SomeD)
  apply (clarsimp simp: valid_blocked_defs st_tcb_at_kh_if_split st_tcb_def2 active_sc_tcb_at_defs
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
  apply (simp add: thread_set_def, wp set_object_wp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunch valid_sched[wp]: cap_move "valid_sched_pred_strong P"

context DetSchedSchedule_AI_det_ext begin

lemma invoke_cnode_valid_sched:
  "\<lbrace>valid_sched and invs and valid_cnode_inv a and simple_sched_action\<rbrace>
     invoke_cnode a
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply wpc
        apply (simp add: liftE_def
               | (wp cancel_badged_sends_valid_sched hoare_vcg_all_lift)+
               | wp (once) hoare_drop_imps
               | wpc)+
  apply (fastforce elim: valid_objs_SendEP_distinct dest: invs_valid_objs)
  done


end

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
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
             split_del: if_split)

lemma reply_push_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
             split_del: if_split)

context DetSchedSchedule_AI begin

crunch scheduler_act[wp]: do_ipc_transfer "(\<lambda>s. P (scheduler_action s)) :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

crunches do_ipc_transfer, handle_fault_reply
  for valid_sched_pred[wp]: "valid_sched_pred_strong P :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres )

lemma send_ipc_not_queued_for_timeout:
  "\<lbrace>not_queued t
    and scheduler_act_not t
    and (\<lambda>s. \<forall>xb. ~ (ko_at (Endpoint (RecvEP (t # xb))) (cap_ep_ptr cap) s))\<rbrace>
      send_ipc True False (cap_ep_badge cap) True crg False tptr (cap_ep_ptr cap)
   \<lbrace>\<lambda>rv. not_queued t  :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  by (wpsimp wp: hoare_drop_imp get_simple_ko_wp split_del: if_split )

end

lemma update_sk_obj_ref_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P scp\<rbrace> update_sk_obj_ref C f ref new \<lbrace>\<lambda>_. sc_tcb_sc_at P scp\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
                wp: get_object_wp get_simple_ko_wp)
  apply (clarsimp simp: partial_inv_def sc_tcb_sc_at_def obj_at_def)
  by (case_tac "C ntfn"; clarsimp simp: a_type_def)

lemma sts_obj_at_neq:
  "\<lbrace>obj_at P t and K (t\<noteq>t')\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. obj_at P t\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: set_object_wp)
     (clarsimp dest!: get_tcb_SomeD simp: pred_tcb_at_def obj_at_def)

lemma set_tcb_sched_context_Some_bound_sc_obj_tcb_at:
  "\<lbrace>\<lambda>s. if t' = t
        then N (pred_map (P (cur_time s)) (sc_refill_cfgs_of s) scp)
        else N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t (Some scp)
   \<lbrace>\<lambda>_ s. N (bound_sc_obj_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps
          elim!: rsubst[of N] cong: conj_cong)

lemma sched_context_donate_bound_sc_obj_tcb_at:
  "\<lbrace>\<lambda>s. N (pred_map (P (cur_time s)) (sc_refill_cfgs_of s) scp)\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>_ s. N (bound_sc_obj_tcb_at (P (cur_time s)) t s)\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_Some_bound_sc_obj_tcb_at
           simp: sched_context_donate_def)

crunches reply_push
  for ct_not_in_q[wp]: "ct_not_in_q"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain"
  and not_cur_thread[wp]: "not_cur_thread t"
  (wp: crunch_wps hoare_vcg_if_lift ignore: set_thread_state test_reschedule)

lemmas set_thread_state_ipc_queued_valid_blocked_except_set
  = set_thread_state_valid_blocked[where ts="BlockedOnReceive ep r_opt pl" for ep r_opt pl, simplified]
    set_thread_state_valid_blocked[where ts="BlockedOnSend ep data" for ep data, simplified]
    set_thread_state_valid_blocked[where ts="BlockedOnNotification ntfn" for ntfn, simplified]
    set_thread_state_valid_blocked[where ts="BlockedOnReply r" for r, simplified]

lemma set_sc_replies_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> (replies \<noteq> [] \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) scp)\<rbrace>
   set_sc_obj_ref sc_replies_update scp replies
   \<lbrace>\<lambda>rv. active_reply_scs\<rbrace>"
  apply (wpsimp wp: update_sched_context_valid_sched_pred)
  by (auto simp: heap_upd_def vs_all_heap_simps split: if_splits elim!: active_reply_scsE)

lemma set_sc_replies_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> (replies \<noteq> [] \<longrightarrow> pred_map active_scrc (sc_refill_cfgs_of s) scp)\<rbrace>
   set_sc_obj_ref sc_replies_update scp replies
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp wp: set_sc_replies_active_reply_scs simp: valid_sched_def)

method reply_push_begin_valid_sched_proof
  = (simp add: reply_push_def
     , intro hoare_seq_ext[OF _ gsc_sp]
     , simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)

lemma reply_push_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and valid_sched_action and not_queued caller and scheduler_act_not caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply reply_push_begin_valid_sched_proof
  apply (intro hoare_seq_ext_skip hoare_when_cases
         ; wpsimp wp: set_thread_state_valid_ready_qs set_thread_state_pred_map_tcb_sts_of
                      get_simple_ko_wp set_thread_state_valid_sched_action)
  by (clarsimp simp: valid_sched_action_no_sc_sched_act_not)

lemma reply_push_valid_release_q[wp]:
  "\<lbrace>valid_release_q and not_in_release_q caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply reply_push_begin_valid_sched_proof
  by (intro hoare_seq_ext_skip hoare_when_cases
      ; wpsimp wp: set_thread_state_valid_release_q get_simple_ko_wp
             simp: valid_release_q_no_sc_not_in_release_q)

lemma reply_push_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and scheduler_act_not caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply reply_push_begin_valid_sched_proof
  by (intro hoare_seq_ext_skip hoare_when_cases
      ; wpsimp wp: set_thread_state_valid_sched_action sched_context_donate_valid_sched_action
                   get_simple_ko_wp
             simp: valid_sched_action_no_sc_sched_act_not)

lemma reply_push_valid_blocked[wp]:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert caller S) s
         \<and> (pred_map runnable (tcb_sts_of s) callee \<longrightarrow> callee \<in> S \<or> callee = cur_thread s)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  apply reply_push_begin_valid_sched_proof
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (rule_tac B="\<lambda>rv s. pred_map_eq sc_callee (tcb_scps_of s) callee
                            \<and> pred_map_eq sc_caller (tcb_scps_of s) caller
                            \<and> valid_blocked_except_set S s
                            \<and> (pred_map runnable (tcb_sts_of s) callee \<longrightarrow> callee \<in> S \<or> callee = cur_thread s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_thread_state_ipc_queued_valid_blocked_except_set
                     hoare_vcg_imp_lift' set_thread_state_pred_map_tcb_sts_of)
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp wp: get_simple_ko_wp\<close>, simp?)+
  by (wpsimp wp: sched_context_donate_valid_blocked set_sc_replies_valid_sched)

lemma reply_push_released_ipc_queues[wp]:
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> active_if_bound_sc_tcb_at caller s
        \<and> (\<forall>scp. can_donate
                 \<longrightarrow> heap_ref_eq scp caller (tcb_scps_of s)
                 \<longrightarrow> sched_context_donate_ipc_queues_precond callee scp s)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  supply if_split[split del]
  apply reply_push_begin_valid_sched_proof
  apply (intro hoare_seq_ext_skip hoare_when_cases
         ; wpsimp wp: set_thread_state_released_ipc_queues get_simple_ko_wp
                      sched_context_donate_released_sc_released_ipc_queues
                      hoare_vcg_all_lift hoare_vcg_imp_lift' set_thread_state_pred_map_tcb_sts_of)
  by (auto simp: vs_all_heap_simps)

lemma reply_push_active_reply_scs[wp]:
  "\<lbrace>active_reply_scs and active_if_bound_sc_tcb_at caller\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. active_reply_scs\<rbrace>"
  apply reply_push_begin_valid_sched_proof
  apply (intro hoare_seq_ext_skip hoare_when_cases
         ; wpsimp wp: get_simple_ko_wp set_sc_replies_active_reply_scs)
  by (clarsimp simp: vs_all_heap_simps)

crunches reply_push
  for ready_or_release[wp]: "ready_or_release"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_push_valid_sched[wp]:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> valid_blocked_except caller s
         \<and> active_if_bound_sc_tcb_at caller s
         \<and> scheduler_act_not caller s
         \<and> not_queued caller s
         \<and> not_in_release_q caller s
         \<and> (pred_map runnable (tcb_sts_of s) callee \<longrightarrow> callee = cur_thread s)
         \<and> (\<forall>scp. can_donate
                  \<longrightarrow> heap_ref_eq scp caller (tcb_scps_of s)
                  \<longrightarrow> sched_context_donate_ipc_queues_precond callee scp s)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def)

lemma set_tcb_sc_update_active_sc_tcb_at': (* this is more usable *)
  "\<lbrace>active_sc_tcb_at t and (is_sc_active scp)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  by (auto simp: vs_all_heap_simps obj_at_def is_sc_active_def
          split: option.splits kernel_object.splits)

lemma set_tcb_sc_update_active_sc_tcb_at_better:
   "\<lbrace>(\<lambda>s. tptr \<noteq> t \<longrightarrow> active_sc_tcb_at t s) and (\<lambda>s. (tptr = t) \<longrightarrow> is_active_sc scp s) \<rbrace>
    set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
    \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  by (auto simp: vs_all_heap_simps obj_at_def)

lemma set_tcb_sc_update_active_sc_tcb_at_better2:
   "\<lbrace>K (tptr \<noteq> t) and active_sc_tcb_at t\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update tptr None
    \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  by (auto simp: vs_all_heap_simps obj_at_def)

lemma sched_context_donate_active_sc_tcb_at:
  "\<lbrace>is_sc_active sc_ptr and active_sc_tcb_at t
    and sc_tcb_sc_at (\<lambda>p. p \<noteq> Some t) sc_ptr\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def assert_opt_def)
  apply (wpsimp wp: set_tcb_sc_update_active_sc_tcb_at_better hoare_vcg_imp_lift'
                    set_tcb_sc_update_active_sc_tcb_at_better2)
  apply (clarsimp simp: is_sc_active_kh_simp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma tcb_sched_context_update_weak_budget_conditions:
  "\<lbrace>is_refill_ready scp and is_refill_sufficient 0 scp \<rbrace>
     set_tcb_obj_ref tcb_sched_context_update tptr (Some scp)
   \<lbrace>\<lambda>r s. budget_ready tptr s \<and> budget_sufficient tptr s\<rbrace>"
  unfolding set_tcb_obj_ref_def
  by (wpsimp wp: set_object_wp get_object_wp
           simp:  vs_all_heap_simps obj_at_kh_kheap_simps sc_at_pred_n_def)

lemma sc_tcb_update_budget_conditions:
  "\<lbrace>is_refill_ready scptr and is_refill_sufficient 0 scptr  \<rbrace>
     set_sc_obj_ref sc_tcb_update scptr (Some tcb_ptr)
   \<lbrace>\<lambda>xaa s. is_refill_ready scptr s \<and> is_refill_sufficient 0 scptr s\<rbrace>"
  apply (wpsimp wp: set_object_wp get_object_wp simp: update_sched_context_def)
  done

lemma sched_context_donate_weak_budget_conditions:
  "\<lbrace>\<lambda>s. is_refill_ready scp s \<and> is_refill_sufficient 0 scp s\<rbrace>
     sched_context_donate scp tcbptr
   \<lbrace>\<lambda>r s. budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: set_object_wp get_object_wp tcb_sched_context_update_weak_budget_conditions sc_tcb_update_budget_conditions)
  apply (wpsimp wp: set_object_wp get_object_wp simp: test_reschedule_def get_sc_obj_ref_def)+
  done

context DetSchedSchedule_AI begin

lemma sched_context_donate_bound_sc_tcb_at_None:
  "\<lbrace>\<lambda>s. pred_map_eq None (tcb_scps_of s) dest \<and> caller_tcb \<noteq> dest\<rbrace>
          sched_context_donate sc_ptr caller_tcb
   \<lbrace>\<lambda>_ s. pred_map_eq None (tcb_scps_of s) dest\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def tcb_at_kh_simps[symmetric])
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp simp: sched_context_donate_def wp: ssc_bound_tcb_at_cases hoare_vcg_imp_lift')
  done

lemma sched_context_donate_released_if_bound:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at ((=) None) callee s \<and> is_sc_active y s \<and> is_refill_ready y s
        \<and> is_refill_sufficient 0 y s\<rbrace>
   sched_context_donate y callee
   \<lbrace>\<lambda>r. released_if_bound_sc_tcb_at callee\<rbrace>"
  apply (clarsimp simp: released_sc_tcb_at_def)
  apply (wpsimp wp: hoare_vcg_disj_lift sched_context_donate_bound_sc_tcb_at_None
                    sched_context_donate_bound_sc_obj_tcb_at
                    sched_context_donate_weak_budget_conditions)
  by (clarsimp simp: obj_at_kh_kheap_simps)

lemma reply_push_released_if_bound:
  "\<lbrace>\<lambda>s. released_if_bound_sc_tcb_at callee s
        \<and> (can_donate \<longrightarrow> released_if_bound_sc_tcb_at caller s)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>r. released_if_bound_sc_tcb_at callee\<rbrace>"
  supply if_split[split del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])+
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>)+
  apply (rule hoare_when_cases; clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp wp: hoare_drop_imps\<close>)+
  apply (wpsimp wp: sched_context_donate_released_if_bound)
  by (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)

lemma set_simple_ko_pred_tcb_at_state:
  "\<lbrace> \<lambda>s. P (pred_tcb_at proj (f s) t s) \<and> (\<forall>new. f s = f (s\<lparr>kheap := kheap s(ep \<mapsto> new)\<rparr>))\<rbrace>
   set_simple_ko g ep v \<lbrace> \<lambda>_ s. P (pred_tcb_at proj (f s) t s) \<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: get_object_wp simp: set_object_def)
  apply (safe; erule rsubst[where P=P];
         clarsimp split: option.splits simp: pred_tcb_at_def obj_at_def fun_upd_def)
  done

lemma RecvEP_queued_ipc_queued_thread:
  "\<lbrakk>kheap s epptr = Some (Endpoint (RecvEP (dest # queue_tail)));
    sym_refs (state_refs_of s)\<rbrakk>
    \<Longrightarrow> ipc_queued_thread dest s"
   apply (subgoal_tac "(dest, EPRecv) \<in> state_refs_of s epptr")
   apply (drule (1) sym_refsD, simp)
   apply (clarsimp simp: vs_all_heap_simps)
   apply (clarsimp simp: state_refs_of_def refs_of_def get_refs_def tcb_st_refs_of_def
                  split: option.splits kernel_object.splits thread_state.splits if_splits)
   apply (clarsimp simp: state_refs_of_def )
   done

\<comment> \<open>The following proofs unbundle valid_sched for send_ipc.
    These lemmas are to support existing unbundled proofs for charge_budget.
    The bundled lemma is preserved below.
    FIXME RT: Find a way to avoid duplication of the structure of the following proofs.
    Alternatively, rework charge_budget proofs to bundle valid_sched invariants.\<close>
lemma send_ipc_valid_ready_qs:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> released_ipc_queues s \<and> valid_sched_action s
        \<and> valid_sender_sc_tcb_at t s \<and> not_queued t s \<and> scheduler_act_not t s
        \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. valid_ready_qs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp wp: set_thread_state_valid_ready_qs)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. valid_ready_qs s \<and> released_ipc_queues s \<and> valid_sched_action s
                           \<and> valid_sender_sc_tcb_at t s \<and> released_if_bound_sc_tcb_at dest s
                           \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)
                           \<and> not_queued t s \<and> scheduler_act_not t s
                           \<and> \<not> pred_map runnable (tcb_sts_of s) dest"
         in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas)
   apply (clarsimp cong: conj_cong)
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) dest \<and> released_if_bound_sc_tcb_at dest s"
          ; clarsimp simp: tcb_sts.pred_map_simps is_blocked_thread_state_defs elim!: released_ipc_queues_blocked_on_recv_ntfn_D)
  apply (rule hoare_seq_ext[OF _ gsc_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. valid_ready_qs s \<and> released_if_bound_sc_tcb_at dest s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: possible_switch_to_valid_ready_qs'' set_thread_state_valid_ready_qs
                     set_thread_state_pred_map_tcb_sts_of)
  apply (simp add: pred_conj_def obj_at_def)
  apply (intro hoare_if[rotated] hoare_when_cases)
     apply clarsimp
    apply (wpsimp wp: sched_context_donate_released_if_bound get_tcb_obj_ref_wp
                simp: valid_sched_action_no_sc_sched_act_not)
    apply (clarsimp simp: is_timeout_fault_opt_def obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)
   apply (wpsimp wp: set_thread_state_valid_ready_qs)
  by (wpsimp wp: reply_push_released_if_bound)

lemma send_ipc_valid_release_q:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> not_in_release_q t s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp wp: set_thread_state_valid_release_q)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. valid_release_q s \<and> not_in_release_q t s \<and> \<not> pred_map runnable (tcb_sts_of s) dest"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas simp: tcb_sts.pred_map_simps)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. valid_release_q s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: set_thread_state_valid_release_q)
  apply (simp add: pred_conj_def obj_at_def)
  by (wpsimp wp: set_thread_state_valid_release_q simp: in_release_q_runnable split: if_splits)

lemma send_ipc_ct_not_in_q:
  "\<lbrace>\<lambda>s. ct_not_in_q s \<and> ct_in_cur_domain s \<and> idle_thread_is_idle s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. ct_not_in_q s \<and> ct_in_cur_domain s
                           \<and> \<not> pred_map runnable (tcb_sts_of s) dest \<and> dest \<noteq> idle_thread s"
         in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas)
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) dest \<and> dest \<noteq> idle_thread s"
          ; clarsimp simp: tcb_sts.pred_map_simps)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. ct_not_in_q s \<and> ct_in_cur_domain s \<and> dest \<noteq> idle_thread s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: possible_switch_to_not_it_ct_not_in_q)
  by wpsimp

lemma send_ipc_valid_sched_action:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> released_ipc_queues s \<and> scheduler_act_not t s
         \<and> valid_sender_sc_tcb_at t s
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp wp: set_thread_state_valid_sched_action)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. valid_sched_action s \<and> scheduler_act_not t s
                           \<and> valid_sender_sc_tcb_at t s
                           \<and> released_if_bound_sc_tcb_at dest s
                           \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas)
   apply (prop_tac "released_if_bound_sc_tcb_at dest s"
          ; clarsimp simp: tcb_sts.pred_map_simps is_blocked_thread_state_defs elim!: released_ipc_queues_blocked_on_recv_ntfn_D)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_. valid_sched_action and released_if_bound_sc_tcb_at dest" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: set_thread_state_valid_sched_action set_thread_state_pred_map_tcb_sts_of
                     hoare_vcg_imp_lift'
               simp: vs_all_heap_simps)
  apply (simp add: pred_conj_def obj_at_def)
  apply (intro hoare_if[rotated] hoare_when_cases)
     apply clarsimp
    apply (wpsimp wp: sched_context_donate_valid_sched_action sched_context_donate_released_if_bound
                      get_tcb_obj_ref_wp
                simp: valid_sched_action_no_sc_sched_act_not)
    apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)
   apply (wpsimp wp: set_thread_state_valid_sched_action)
  by (wpsimp wp: reply_push_released_if_bound)

lemma send_ipc_ct_in_cur_domain:
  "send_ipc block call badge can_grant can_grant_reply can_donate t epptr \<lbrace>ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. ct_in_cur_domain s \<and> \<not> pred_map runnable (tcb_sts_of s) dest"
         in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas hoare_vcg_disj_lift simp: valid_sched_def)
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) dest"; clarsimp simp: tcb_sts.pred_map_simps)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. ct_in_cur_domain s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply wpsimp
  by wpsimp

lemma send_ipc_valid_blocked:
  "\<lbrace>\<lambda>s. \<comment> \<open>In do_reply_transfer, valid_blocked might be broken for handle_timeout\<close>
        valid_blocked_except_set (insert t S) s
         \<comment> \<open>Timeout faults can come from threads other than the current thread
             ; see handle_timeout in do_reply_transfer\<close>
         \<and> (valid_blocked_tcb_at t s \<or> block \<and> pred_map bound (tcb_faults_of s) t)\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. valid_blocked_except_set S :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp
          ; wpsimp wp: set_thread_state_ipc_queued_valid_blocked_except_set
          ; clarsimp elim!: valid_blocked_divided_threadE)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. valid_blocked_except_set (insert t S) s
                           \<and> (valid_blocked_tcb_at t s \<or> block \<and> pred_map bound (tcb_faults_of s) t)
                           \<and>  \<not> pred_map runnable (tcb_sts_of s) dest"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas hoare_vcg_disj_lift)
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) dest"; clarsimp simp: tcb_sts.pred_map_simps)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. valid_blocked_except_set S s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: possible_switch_to_valid_blocked set_thread_state_valid_blocked)
  apply (simp add: pred_conj_def obj_at_def)
  apply (intro hoare_if[rotated] hoare_when_cases)
     apply (clarsimp simp: vs_all_heap_simps elim!: valid_blocked_divided_threadE)
    apply (wpsimp wp: sched_context_donate_valid_blocked get_tcb_obj_ref_wp)
    apply (clarsimp simp: vs_all_heap_simps valid_blocked_thread_def elim!: valid_blockedE')
   apply wpsimp
  by wpsimp

lemma send_ipc_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)
         \<and> valid_sender_sc_tcb_at t s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp wp: set_thread_state_released_ipc_queues simp: is_blocked_thread_state_defs)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. released_ipc_queues s
                            \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)
                            \<and> valid_sender_sc_tcb_at t s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_. released_ipc_queues" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: set_thread_state_released_ipc_queues simp: is_blocked_thread_state_defs)
  apply (simp add: pred_conj_def obj_at_def)
  apply (intro hoare_if[rotated] hoare_when_cases)
     apply clarsimp
    apply (wpsimp wp: sched_context_donate_released_sc_released_ipc_queues get_tcb_obj_ref_wp)
    apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps)
   apply (wpsimp wp: set_thread_state_released_ipc_queues simp: is_blocked_thread_state_defs)
  apply wpsimp
  by (auto simp: vs_all_heap_simps is_blocked_thread_state_defs is_timeout_fault_opt_def
          split: if_splits option.splits)

lemma send_ipc_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> active_if_bound_sc_tcb_at t s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp; wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. active_reply_scs s \<and> active_if_bound_sc_tcb_at t s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. active_reply_scs s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply wpsimp
  by wpsimp

crunches reply_push
  for tcb_at[wp]: "tcb_at t"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps)

crunches send_ipc
  for ready_or_release[wp]: "ready_or_release :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps)

lemmas send_ipc_valid_sched_unbundled
  = send_ipc_valid_ready_qs send_ipc_valid_release_q send_ipc_ct_not_in_q
    send_ipc_valid_sched_action send_ipc_ct_in_cur_domain send_ipc_valid_blocked
    send_ipc_released_ipc_queues send_ipc_active_reply_scs

lemma send_ipc_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> idle_thread_is_idle s
         \<comment> \<open>In do_reply_transfer, valid_blocked might be broken for handle_timeout\<close>
         \<and> valid_blocked_except t s
         \<comment> \<open>Timeout faults can come from threads other than the current thread
             ; see handle_timeout in do_reply_transfer\<close>
         \<and> (valid_blocked_tcb_at t s \<or> block \<and> pred_map bound (tcb_faults_of s) t)
         \<comment> \<open>If the sender offers to donate, it must have a sched context to donate\<close>
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)
         \<and> valid_sender_sc_tcb_at t s
         \<and> scheduler_act_not t s
         \<and> not_queued t s
         \<and> not_in_release_q t s\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate t epptr
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  \<comment> \<open>We can prove this lemma two different ways.\<close>
  apply (rule conj_absorb[THEN iffD1, OF conjI])
  \<comment> \<open>Firstly, we simply use the lemmas above, which unbundle valid_sched for send_ipc.\<close>
   apply (wpsimp wp: send_ipc_valid_sched_unbundled simp: valid_sched_def)
   apply (clarsimp simp: vs_all_heap_simps)
  \<comment> \<open>Secondly, we can independently perform a bundled proof. Although this is redundant, this
      might be preferable to the unbundled proofs, since it avoids duplication of proof structure,
      and checks faster than the collection of unbundled proofs. However, it is currently not
      possible to drop the unbundled lemmas, since they are needed for existing unbundled
      charge_budget lemmas.\<close>
  unfolding send_ipc_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac "\<forall>dest queue. ep \<noteq> RecvEP (dest # queue)"; clarsimp)
   apply (case_tac "\<exists>q. ep = RecvEP q", elim exE, (case_tac q; simp))
   apply (case_tac ep; simp
          ; wpsimp wp: set_thread_state_ipc_queued_valid_blocked_except_set
                       set_thread_state_valid_sched_except_blocked
                 simp: valid_sched_valid_sched_except_blocked scheduler_act_not_def
          ; clarsimp elim!: valid_blocked_divided_threadE)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp], simp add: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply ((case_tac recv_state; clarsimp), rename_tac ep_ptr reply_opt)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_ s. valid_sched_except_blocked s \<and> valid_blocked_except t s
                           \<and> released_if_bound_sc_tcb_at dest s
                           \<and> (valid_blocked_tcb_at t s \<or> block \<and> pred_map bound (tcb_faults_of s) t)
                           \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> timeout_faulted_tcb_at t s)
                           \<and> valid_sender_sc_tcb_at t s
                           \<and> scheduler_act_not t s \<and> not_queued t s \<and> not_in_release_q t s
                           \<and> dest \<noteq> idle_thread s
                           \<and> \<not> pred_map runnable (tcb_sts_of s) dest"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_unlink_tcb.valid_sched_lemmas hoare_vcg_disj_lift simp: valid_sched_def)
   apply (simp flip: id_def)? \<comment> \<open>Unifier did something weird here\<close>
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) dest \<and> released_if_bound_sc_tcb_at dest s"
          , clarsimp simp: tcb_sts.pred_map_simps elim!: released_ipc_queues_blocked_on_recv_ntfn_E1)
   apply (prop_tac "dest \<noteq> idle_thread s", clarsimp simp: vs_all_heap_simps)
   apply (clarsimp elim!: released_ipc_queuesE)
   apply (clarsimp simp: vs_all_heap_simps split: if_splits)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule_tac B="\<lambda>_ s. valid_sched s \<and> released_if_bound_sc_tcb_at dest s \<and> dest \<noteq> idle_thread s" in hoare_seq_ext)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext[OF _ assert_inv])
   apply (wpsimp wp: set_thread_state_possible_switch_to_valid_sched)
  apply (simp add: pred_conj_def obj_at_def valid_blocked_thread_def)
  apply (intro hoare_if[rotated] hoare_when_cases)
     apply (clarsimp simp: valid_sched_valid_sched_except_blocked vs_all_heap_simps
                    elim!: valid_blockedE')
    apply (wpsimp wp: sched_context_donate_valid_sched sched_context_donate_released_if_bound
                      get_tcb_obj_ref_wp)
    apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps
                          valid_sched_valid_sched_except_blocked
                   elim!: valid_blockedE')
   apply (wpsimp wp: set_thread_state_Inactive_not_queued_valid_sched simp: valid_sched_def)
  apply (wpsimp wp: reply_push_released_if_bound)
   \<comment> \<open>Focus on just the assumption we need to speed up the proof\<close>
  by (match premises in H: \<open>timeout_faulted_tcb_at t s \<and> active_sc_tcb_at t s \<or> released_if_bound_sc_tcb_at t s\<close>
                    and D: \<open>can_donate \<longrightarrow> _\<close> for s
      \<Rightarrow> \<open>insert D H, fastforce simp: vs_all_heap_simps\<close>)

lemma send_fault_ipc_valid_sched_misc[wp]:
  "send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                            (idle_thread s) (last_machine_time_of s) (etcbs_of s) (sc_refill_cfgs_of s)\<rbrace>"
  unfolding send_fault_ipc_def by wpsimp

lemma thread_set_fault_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
        \<and> (timeout_faulted_tcb_at t s \<and> blocked_on_send_tcb_at t s
           \<longrightarrow> is_timeout_fault fault \<or> released_if_bound_sc_tcb_at t s)\<rbrace>
   thread_set (tcb_fault_update (\<lambda>_. Some fault)) t
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  apply (wpsimp wp: thread_set_fault_valid_sched_pred)
  by (clarsimp simp: heap_upd_def is_timeout_fault_opt_def vs_all_heap_simps elim!: released_ipc_queuesE)

lemma thread_set_fault_tcb_at':
  "\<lbrace>\<lambda>s. if t' = t then N (P fault_opt) else N (fault_tcb_at' P t' s)\<rbrace>
   thread_set (tcb_fault_update (\<lambda>_. fault_opt)) t
   \<lbrace>\<lambda>_ s. N (fault_tcb_at' P t' s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  by (clarsimp simp: vs_all_heap_simps)

lemma send_fault_ipc_valid_ready_qs:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> released_ipc_queues s \<and> valid_sched_action s
         \<and> (is_timeout_fault fault \<and> active_sc_tcb_at t s \<or> released_if_bound_sc_tcb_at t s)
         \<and> not_queued t s \<and> scheduler_act_not t s
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> is_timeout_fault fault)\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. valid_ready_qs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: send_ipc_valid_ready_qs thread_set_fault_released_ipc_queues
                    hoare_vcg_disj_lift thread_set_fault_tcb_at' hoare_vcg_const_imp_lift)
  by (auto simp: vs_all_heap_simps is_timeout_fault_opt_def split: option.splits)

lemma send_fault_ipc_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q t\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def by (wpsimp wp: send_ipc_valid_release_q)

lemma send_fault_ipc_ct_not_in_q:
  "\<lbrace>ct_not_in_q and ct_in_cur_domain and idle_thread_is_idle\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def by (wpsimp wp: send_ipc_ct_not_in_q)

lemma send_fault_ipc_valid_sched_action:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> released_ipc_queues s \<and> scheduler_act_not t s
         \<and> (is_timeout_fault fault \<and> active_sc_tcb_at t s \<or> released_if_bound_sc_tcb_at t s)
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> is_timeout_fault fault)\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: send_ipc_valid_sched_action thread_set_fault_released_ipc_queues
                    hoare_vcg_disj_lift thread_set_fault_tcb_at' hoare_vcg_const_imp_lift)
  by (auto simp: vs_all_heap_simps is_timeout_fault_opt_def split: option.splits)

lemma send_fault_ipc_ct_in_cur_domain:
  "send_fault_ipc t handler_cap fault can_donate \<lbrace>ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def by (wpsimp wp: send_ipc_ct_in_cur_domain)

lemma send_fault_ipc_valid_blocked:
  "\<lbrace>\<lambda>s. \<comment> \<open>In do_reply_transfer, valid_blocked might be broken for handle_timeout\<close>
        valid_blocked_except_set (insert t S) s
         \<comment> \<open>Timeout faults can come from threads other than the current thread
             ; see handle_timeout in do_reply_transfer\<close>
         \<and> (valid_blocked_tcb_at t s \<or> is_ep_cap handler_cap)\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. valid_blocked_except_set S :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: send_ipc_valid_blocked thread_set_fault_valid_sched_pred)
  apply (intro conjI allI impI
         ; clarsimp simp: heap_upd_def elim!: valid_blocked_divided_threadE)
  by (auto simp: vs_all_heap_simps valid_blocked_thread_def)

lemma send_fault_ipc_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s
         \<and> (is_timeout_fault fault \<and> active_sc_tcb_at t s \<or> released_if_bound_sc_tcb_at t s)
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> is_timeout_fault fault)\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: send_ipc_released_ipc_queues thread_set_fault_released_ipc_queues
                    hoare_vcg_disj_lift thread_set_fault_tcb_at' hoare_vcg_const_imp_lift)
  by (auto simp: vs_all_heap_simps is_timeout_fault_opt_def split: option.splits)

lemma send_fault_ipc_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> active_if_bound_sc_tcb_at t s\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def by (wpsimp wp: send_ipc_active_reply_scs)

lemmas send_fault_ipc_valid_sched_unbundled
  = send_fault_ipc_valid_ready_qs send_fault_ipc_valid_release_q send_fault_ipc_ct_not_in_q
    send_fault_ipc_valid_sched_action send_fault_ipc_ct_in_cur_domain
    send_fault_ipc_valid_blocked send_fault_ipc_released_ipc_queues send_fault_ipc_active_reply_scs

lemma send_fault_ipc_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> idle_thread_is_idle s
         \<comment> \<open>In do_reply_transfer, valid_blocked might be broken for handle_timeout\<close>
         \<and> valid_blocked_except t s
         \<comment> \<open>Timeout faults can come from threads other than the current thread
             ; see handle_timeout in do_reply_transfer\<close>
         \<and> (valid_blocked_tcb_at t s \<or> is_ep_cap handler_cap)
         \<comment> \<open>If the sender offers to donate, it must have a sched context to donate\<close>
         \<and> (can_donate \<longrightarrow> pred_map bound (tcb_scps_of s) t \<and> \<not> is_timeout_fault fault)
         \<and> (is_timeout_fault fault \<and> active_sc_tcb_at t s \<or> released_if_bound_sc_tcb_at t s)
         \<and> scheduler_act_not t s
         \<and> not_queued t s
         \<and> not_in_release_q t s\<rbrace>
   send_fault_ipc t handler_cap fault can_donate
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: send_ipc_valid_sched thread_set_fault_valid_sched_pred)
  by (auto simp: valid_sched_def heap_upd_def vs_all_heap_simps
                 is_timeout_fault_def is_timeout_fault_opt_def
           elim!: released_ipc_queuesE valid_blocked_divided_threadE
           split: if_splits)

lemma handle_timeout_valid_sched_misc[wp]:
  "handle_timeout t timeout
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                            (idle_thread s) (last_machine_time_of s) (etcbs_of s) (sc_refill_cfgs_of s)\<rbrace>"
  unfolding handle_timeout_def by wpsimp

lemma handle_timeout_valid_ready_qs:
  "\<lbrace>\<lambda>s. valid_ready_qs s \<and> released_ipc_queues s \<and> valid_sched_action s
         \<and> active_if_bound_sc_tcb_at t s \<and> not_queued t s \<and> scheduler_act_not t s
         \<and> is_timeout_fault timeout\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. valid_ready_qs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  by (wpsimp wp: send_fault_ipc_valid_ready_qs)

lemma handle_timeout_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q t\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def by (wpsimp wp: send_fault_ipc_valid_release_q)

lemma handle_timeout_ct_not_in_q:
  "\<lbrace>ct_not_in_q and ct_in_cur_domain and idle_thread_is_idle\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def by (wpsimp wp: send_fault_ipc_ct_not_in_q)

lemma handle_timeout_valid_sched_action:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> released_ipc_queues s \<and> scheduler_act_not t s
        \<and> active_if_bound_sc_tcb_at t s \<and> is_timeout_fault timeout\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  by (wpsimp wp: send_fault_ipc_valid_sched_action)

lemma handle_timeout_ct_in_cur_domain:
  "handle_timeout t timeout \<lbrace>ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def by (wpsimp wp: send_fault_ipc_ct_in_cur_domain)

lemma handle_timeout_valid_blocked:
  "\<lbrace>\<lambda>s. valid_blocked_except_set (insert t S) s\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. valid_blocked_except_set S :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def by (wpsimp wp: send_fault_ipc_valid_blocked)

lemma handle_timeout_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> active_if_bound_sc_tcb_at t s \<and> is_timeout_fault timeout\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  by (wpsimp wp: send_fault_ipc_released_ipc_queues)

lemma handle_timeout_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> active_if_bound_sc_tcb_at t s\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def by (wpsimp wp: send_fault_ipc_active_reply_scs)

lemmas handle_timeout_valid_sched_bundled
  = handle_timeout_valid_ready_qs handle_timeout_valid_release_q handle_timeout_ct_not_in_q
    handle_timeout_valid_sched_action handle_timeout_ct_in_cur_domain handle_timeout_valid_blocked
    handle_timeout_released_ipc_queues handle_timeout_active_reply_scs

lemma handle_timeout_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched_except_blocked s
         \<and> idle_thread_is_idle s
         \<and> valid_blocked_except t s
         \<and> active_if_bound_sc_tcb_at t s
         \<and> scheduler_act_not t s
         \<and> not_queued t s
         \<and> not_in_release_q t s
         \<and> is_timeout_fault timeout\<rbrace>
   handle_timeout t timeout
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  by (wpsimp wp: send_fault_ipc_valid_sched)

end

lemma thread_set_is_sc_active[wp]:
  "thread_set f t \<lbrace>\<lambda>s. Q (is_sc_active scp s)\<rbrace>"
  by (wpsimp wp: thread_set_wp, clarsimp simp: is_sc_active_def dest!: get_tcb_SomeD)

lemma send_fault_ipc_error_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_cur_thread[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

context DetSchedSchedule_AI begin

lemma send_ipc_not_queued:
  "\<lbrace>not_queued tcb_ptr and scheduler_act_not tcb_ptr
    and (\<lambda>s. \<forall>qtail. \<not> pred_map_eq (tcb_ptr # qtail) (ep_recv_qs_of s) epptr)\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate tptr epptr
   \<lbrace>\<lambda>rv. not_queued tcb_ptr:: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  apply (wpsimp wp: hoare_drop_imp get_simple_ko_wp
         split_del: if_split
              simp: do_ipc_transfer_def do_normal_transfer_def vs_all_heap_simps
                    obj_at_kh_kheap_simps)
  done

crunches reply_push
  for not_in_release_q'[wp]: "\<lambda>s. not_in_release_q t s"
  (wp: crunch_wps simp: crunch_simps)

lemma send_ipc_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace>
   send_ipc True False badge can_grant can_grant_reply can_donate tptr epptr
   \<lbrace>\<lambda>rv. not_in_release_q t::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def )
  by (wpsimp wp: hoare_drop_imp get_simple_ko_wp hoare_vcg_all_lift
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

lemma transfer_caps_scheduler_act_not:
  "\<lbrace>scheduler_act_not t and (\<lambda>s. \<forall>xb. \<not>ko_at (Endpoint (RecvEP (t # xb))) epptr s)\<rbrace>
   send_ipc True False badge can_grant can_grant_reply can_donate tptr epptr
   \<lbrace>\<lambda>rv. scheduler_act_not t::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def )
  apply (wpsimp wp: hoare_drop_imps
         split_del: if_split
              simp: do_ipc_transfer_def do_normal_transfer_def do_fault_transfer_def)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)
    apply clarsimp
    apply (wpsimp wp: get_simple_ko_wp)+
  done

lemma send_fault_ipc_not_queued:
  "\<lbrace>invs and not_queued t and st_tcb_at (not ipc_queued_thread_state) t and scheduler_act_not t\<rbrace>
   send_fault_ipc tptr handler_cap fault can_donate
   \<lbrace>\<lambda>rv. not_queued t::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift_R send_ipc_not_queued
              simp: obj_at_kh_kheap_simps vs_all_heap_simps)
  apply (subgoal_tac "st_tcb_at ipc_queued_thread_state t s")
   apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  apply (subgoal_tac "ko_at (Endpoint (RecvEP (t # qtail))) x s")
   apply (rule ep_queued_st_tcb_at; clarsimp?)
    apply assumption
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (rule refl)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def pred_neg_def)
  done

lemma send_fault_ipc_not_queued_not_ep_queued:
  "\<lbrace>not_queued t and scheduler_act_not t
    and (\<lambda>s. \<forall>qtail. \<not> pred_map_eq (t # qtail) (ep_recv_qs_of s) (cap_ep_ptr handler_cap))\<rbrace>
   send_fault_ipc t' handler_cap fault can_donate
   \<lbrace>\<lambda>rv. not_queued t :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wpsimp wp: thread_set_wp send_ipc_not_queued simp: obj_at_kh_kheap_simps vs_all_heap_simps)
  done

lemma send_fault_ipc_not_in_release_q:
  "\<lbrace>not_in_release_q t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate \<lbrace>\<lambda>rv. not_in_release_q t::'state_ext state \<Rightarrow> _\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R send_ipc_not_in_release_q)+ | wpc)+

lemma send_fault_ipc_scheduler_act_not:
  "\<lbrace>invs and st_tcb_at active t and scheduler_act_not t\<rbrace>
   send_fault_ipc tptr handler_cap fault can_donate
   \<lbrace>\<lambda>rv. scheduler_act_not t::'state_ext state \<Rightarrow> _\<rbrace>"
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

lemma reply_push_weak_valid_sched_action_no_donation:
  "\<lbrace> weak_valid_sched_action and
     scheduler_act_not thread\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_weak_valid_sched_action hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma reply_push_valid_blocked_no_donation:
  "\<lbrace> valid_blocked_except_set (insert thread S)\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked_remove hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma reply_push_valid_blocked_no_donation':
  "\<lbrace> valid_blocked_except_set S\<rbrace>
   reply_push thread dest ya False
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked_remove hoare_drop_imps
                 update_sk_obj_ref_lift)

lemma weak_valid_sched_action_scheduler_action_not:
  "weak_valid_sched_action s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s \<Longrightarrow> scheduler_act_not t s"
  by (clarsimp simp: weak_valid_sched_action_def scheduler_act_not_def tcb_at_kh_simps pred_map_def)

lemma valid_release_q_not_in_release_q_not_runnable:
  "valid_release_q s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s \<Longrightarrow> not_in_release_q t s"
  by (clarsimp simp: valid_release_q_def not_in_release_q_def  tcb_at_kh_simps pred_map_def, fastforce)

lemma valid_ready_qs_not_queued_not_runnable:
  "valid_ready_qs s \<Longrightarrow> st_tcb_at (Not \<circ> runnable) t s \<Longrightarrow> not_queued t s"
  by (clarsimp simp: valid_ready_qs_def not_queued_def tcb_at_kh_simps pred_map_def, fastforce)

crunch not_in_release_q[wp]: reply_remove "\<lambda>s::('state_ext state). not_in_release_q a s"
  (wp: crunch_wps tcb_release_remove_not_in_release_q')

lemma reply_unlink_tcb_ct_in_state:
  "\<lbrace>ct_in_state test and (\<lambda>s. (\<forall>t. reply_tcb_reply_at ((=) (Some t)) r s \<longrightarrow> cur_thread s \<noteq> t \<or> test (Inactive)))\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_. ct_in_state test :: ('state_ext state) \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp wp: sts_ctis_neq set_simple_ko_wp gts_wp get_simple_ko_wp)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def reply_at_ppred_def)
  done

lemma reply_remove_valid_sched_misc[wp]:
  "reply_remove caller reply
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (last_machine_time_of s) (etcbs_of s)
          (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp simp: reply_remove_def)

lemma reply_remove_ct_in_state:
  "\<lbrace>ct_in_state P and (\<lambda>s. \<forall>t. reply_tcb_reply_at ((=) (Some t)) r s \<longrightarrow> cur_thread s \<noteq> t \<or> P Inactive)\<rbrace>
     reply_remove t r
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding reply_remove_def
  apply (wpsimp wp: reply_unlink_tcb_ct_in_state)
  apply (wpsimp wp: ct_in_state_thread_state_lift sched_context_donate_cur_thread
                    hoare_vcg_imp_lift' hoare_vcg_all_lift get_simple_ko_wp | wps)+
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma reply_at_ppred_eq_commute:
  "reply_at_ppred proj ((=) v) = reply_at_ppred proj (\<lambda>x. x = v)"
  by (intro ext) (auto simp: reply_at_ppred_def obj_at_def)

lemmas reply_unlink_tcb_inactive'[wp]
  = reply_unlink_tcb_inactive[unfolded pred_map_eq_normalise obj_at_kh_kheap_simps]

lemma reply_remove_inactive[wp]:
  "\<lbrace>\<top>\<rbrace> reply_remove t r \<lbrace>\<lambda>_. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (wpsimp simp: reply_remove_def)

lemmas reply_remove_inactive'[wp]
  = reply_remove_inactive[unfolded pred_map_eq_normalise obj_at_kh_kheap_simps]

(* FIXME RT: move *)
lemma gets_the_sp:
  "\<lbrace>P\<rbrace> gets_the f \<lbrace>\<lambda>rv s. f s = Some rv \<and> P s\<rbrace>"
  by wpsimp

lemma sched_context_donate_tcb_scps_of_retract:
  "\<lbrace>\<lambda>s. heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s) \<and> pred_map_eq None (tcb_scps_of s) t\<rbrace>
   sched_context_donate scp t
   \<lbrace>\<lambda>rv s. heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_pred update_sc_tcb_valid_sched_pred get_sc_obj_ref_wp
              simp: sched_context_donate_def obj_at_def heap_upd_def)
  by (auto simp: vs_all_heap_simps pred_map_simps elim!: heap_refs_retractE split: if_splits)

lemma reply_remove_tcb_scps_of_retract:
  "\<lbrace>\<lambda>s. heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)\<rbrace>
   reply_remove caller reply
   \<lbrace>\<lambda>rv s. heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)\<rbrace>"
  unfolding reply_remove_def
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, (simp only: K_bind_def)?)+
  apply (rule hoare_seq_ext_skip[rotated], wpsimp)
  apply (case_tac r_sc_opt, wpsimp, simp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gsc_sp], clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule hoare_seq_ext_skip, wpsimp)
  by (wpsimp wp: sched_context_donate_tcb_scps_of_retract)

lemma reply_remove_active_if_bound_sc_tcb_at:
  "\<lbrace>\<lambda>s. active_if_bound_sc_tcb_at t s \<and> active_reply_scs s\<rbrace>
   reply_remove t r
   \<lbrace>\<lambda>rv s. active_if_bound_sc_tcb_at t s\<rbrace>"
  unfolding reply_remove_def
  apply (wpsimp wp: sched_context_donate_bound_sc_obj_tcb_at
                    hoare_vcg_if_lift2 hoare_vcg_const_imp_lift
                    hoare_vcg_disj_lift sched_context_donate_bound_sc_tcb_at_None
                    get_tcb_obj_ref_wp get_simple_ko_wp
              simp: reply_remove_def)
  by (elim disjE; clarsimp simp: obj_at_def cong: conj_cong
      ; fastforce dest!: sc_with_reply_SomeD simp: active_reply_scs_defs vs_all_heap_simps)

lemma set_thread_state_idle_thread_is_idle[wp]:
  "\<lbrace>\<lambda>s. if t = idle_thread s then idle st else idle_thread_is_idle s\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv s. idle_thread_is_idle s\<rbrace>"
  apply (wpsimp wp: set_thread_state_valid_sched_pred)
  by (auto simp: vs_all_heap_simps)

lemma reply_remove_idle_thread_is_idle[wp]:
  "\<lbrace>\<lambda>s.  idle_thread_is_idle s \<and> t \<noteq> idle_thread s\<rbrace> reply_remove t reply \<lbrace>\<lambda>rv s. idle_thread_is_idle s\<rbrace>"
  unfolding reply_remove_def reply_unlink_tcb_def
  by (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+ wpsimp

abbreviation (input)
  "do_reply_transfer_pred receiver s
   \<equiv> not_in_release_q receiver s \<and> not_queued receiver s \<and> scheduler_act_not receiver s
      \<and> valid_blocked_except receiver s \<and> valid_sched_except_blocked s
      \<and> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)
      \<and> idle_thread_is_idle s
      \<and> receiver \<noteq> idle_thread s
      \<and> active_if_bound_sc_tcb_at receiver s
      \<and> current_time_bounded 1 s"

lemma valid_sched_active_reply_scs[simp,elim!]:
  "valid_sched_2 wk_vsa vbl ctime cdom ct it queues rlq sa lmt etcbs tcb_sts tcb_scps tcb_faults sc_refill_cfgs sc_repls
   \<Longrightarrow> active_reply_scs_2 sc_repls sc_refill_cfgs"
  by (simp add: valid_sched_def)

lemma do_reply_transfer_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s \<and> valid_objs s \<and> valid_replies s \<and> valid_idle s \<and> sym_refs (state_refs_of s)
         \<and> current_time_bounded 1 s\<rbrace>
   do_reply_transfer sender reply grant
   \<lbrace>\<lambda>rv. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (case_tac recv_opt, wpsimp, clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac receiver state)
  apply (case_tac "\<forall>r'. state \<noteq> BlockedOnReply r'", solves \<open>wpsimp\<close>, clarsimp)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule_tac S="r'=reply" in hoare_gen_asm''; clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule_tac B="\<lambda>_ s. valid_sched s
                            \<and> pred_map_eq Inactive (tcb_sts_of s) receiver
                            \<and> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)
                            \<and> idle_thread_is_idle s
                            \<and> receiver \<noteq> idle_thread s
                            \<and> active_if_bound_sc_tcb_at receiver s
                            \<and> current_time_bounded 1 s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_remove_valid_sched reply_remove_tcb_scps_of_retract
                     reply_remove_active_if_bound_sc_tcb_at
                     reply_remove_tcb_scps_of_retract)
   apply (apply_conjunct \<open>rule released_ipc_queues_blocked_on_reply_E1[OF valid_sched_released_ipc_queues]\<close>
          ; fastforce simp: vs_all_heap_simps valid_idle_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ thread_get_inv])
  \<comment> \<open>valid_blocked might be broken here for receiver\<close>
  apply (rule_tac B="\<lambda>_ s. do_reply_transfer_pred receiver s" in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_thread_state_not_runnable_valid_sched_except_blocked
                     set_thread_state_valid_blocked_const
                     thread_set_fault_valid_sched_pred
               simp: if_distrib)
   apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) receiver", clarsimp simp: vs_all_heap_simps)
   apply (prop_tac "not_queued receiver s"
          , erule valid_ready_qs_contrap[OF valid_sched_valid_ready_qs], simp)
   apply (prop_tac "not_in_release_q receiver s"
          , clarsimp simp: valid_release_q_def in_release_q_def dest!: valid_sched_valid_release_q)
   apply (prop_tac "scheduler_act_not receiver s", clarsimp simp: valid_sched_not_runnable_scheduler_act_not)
   apply (clarsimp simp: valid_sched_def elim!: released_ipc_queuesE)
   apply (clarsimp simp: vs_all_heap_simps heap_upd_def split: if_splits)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac "runnable state \<longrightarrow> sc_opt = None"
         ; clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
   apply (wpsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise valid_sched_def)
   apply (fastforce elim!: valid_blockedE' simp: vs_all_heap_simps)
  apply (rename_tac scp)
  apply (rule_tac B="\<lambda>_ s. pred_map_eq (Some scp) (tcb_scps_of s) receiver
                           \<and> pred_map runnable (tcb_sts_of s) receiver
                           \<and> do_reply_transfer_pred receiver s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: refill_unblock_check_valid_sched_except_blocked hoare_vcg_disj_lift)
   apply (clarsimp simp: pred_map_eq_pred_mapE)
   apply (drule (1) heap_refs_retractD[rotated])+
   apply (clarsimp simp: sc_tcbs.pred_map_simps)
  apply (intro hoare_seq_ext[OF _ get_sched_context_sp]
               hoare_seq_ext[OF _ gets_sp]
               hoare_seq_ext[OF _ gets_the_sp]
               hoare_if)
    apply (wpsimp wp: possible_switch_to_valid_sched_strong)
    apply (clarsimp simp: valid_sched_valid_sched_except_blocked vs_all_heap_simps refill_ready_def obj_at_def)
   apply (wpsimp wp: handle_timeout_valid_sched simp: is_timeout_fault_def)
  apply (wpsimp wp: postpone_valid_sched)
  apply (prop_tac "tp = receiver", frule (1) heap_refs_retractD, clarsimp simp: sc_tcbs.pred_map_simps)
  by (clarsimp simp: active_bound_sc_tcb_at)

lemma handle_no_fault_valid_sched:
  "\<lbrace>valid_sched and not_queued thread and not_in_release_q thread and scheduler_act_not thread\<rbrace>
   handle_no_fault thread
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_no_fault_def
  by (wpsimp wp: set_thread_state_valid_sched, simp add: valid_sched_def)

lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and invs and st_tcb_at active thread and scheduler_act_not thread
      and not_queued thread and not_in_release_q thread and released_if_bound_sc_tcb_at thread
      and K (\<not> is_timeout_fault ex)\<rbrace>
   handle_fault thread ex
   \<lbrace>\<lambda>rv. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: handle_fault_def unless_def)
  apply (rule hoare_seq_ext[OF _ gets_the_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule_tac B="\<lambda>_. valid_sched and not_queued thread and not_in_release_q thread and scheduler_act_not thread" in hoare_seq_ext
         , wpsimp wp: handle_no_fault_valid_sched)
  apply (wpsimp wp: send_fault_ipc_valid_sched
                    send_fault_ipc_not_queued send_fault_ipc_not_in_release_q
                    send_fault_ipc_scheduler_act_not
              simp: valid_idle_idle_thread_is_idle[OF invs_valid_idle]
              cong: conj_cong)
  by (auto simp: valid_sched_valid_sched_except_blocked obj_at_kh_kheap_simps vs_all_heap_simps
                 pred_neg_def valid_blockedD)
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

crunches cancel_ipc
  for active_sc_tcb_at: "active_sc_tcb_at t::('state_ext state) \<Rightarrow> _"
  (wp: hoare_drop_imp crunch_wps)

end

lemma set_thread_state_st_tcb_at:
  " P ts \<Longrightarrow>
    \<lbrace>st_tcb_at \<top> tcbptr\<rbrace>
      set_thread_state tcbptr ts
    \<lbrace>\<lambda>rv s. st_tcb_at P tcbptr s\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: is_schedulable_wp set_object_wp)
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

lemma tcb_sched_context_update_active_sc_tcb_at:
  "\<lbrace>is_sc_active sc_ptr\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr)
   \<lbrace>\<lambda>r. active_sc_tcb_at tcb_ptr\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: vs_all_heap_simps is_sc_active_kh_simp dest!: get_tcb_SomeD)

lemma sched_context_donate_bound_sc_tcb_at[wp]:
  "\<lbrace>\<top>\<rbrace> sched_context_donate scp tptr \<lbrace>\<lambda>rv. bound_sc_tcb_at ((=) (Some scp)) tptr\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: ssc_bound_tcb_at')

lemma sched_context_donate_sc_tcb_sc_at[wp]:
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

lemma maybe_donate_sc_valid_sched_misc[wp]:
  "maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s) (cur_domain s)
           (cur_thread s) (idle_thread s) (last_machine_time_of s) (etcbs_of s) (tcb_sts_of s)
           (sc_replies_of s)\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: hoare_drop_imp)

lemma sched_context_resume_cond_released_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr and sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr
    and (\<lambda>s. pred_map runnable (tcb_sts_of s) tcbptr)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>rv s. active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> released_sc_tcb_at tcbptr s\<rbrace>"
  unfolding sched_context_resume_def
  apply wpsimp
              apply (rule_tac Q="\<lambda>r. DetSchedInvs_AI.in_release_q tcbptr" in hoare_strengthen_post[rotated])
               apply (clarsimp simp: pred_neg_def not_in_release_q_def in_release_q_def)
              apply (wpsimp wp: postpone_in_release_q is_schedulable_wp
                          simp: thread_get_def)+
  apply (intro conjI; intro allI impI; clarsimp)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_schedulable_bool_def2 vs_all_heap_simps
                  dest!: get_tcb_SomeD)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_schedulable_bool_def2 vs_all_heap_simps
                        sc_at_pred_n_def
                 dest!: get_tcb_SomeD)
  done

lemma maybe_donate_sc_cond_released_sc_tcb_at:
  "\<lbrace>released_if_bound_sc_tcb_at tcbptr and st_tcb_at runnable tcbptr\<rbrace>
     maybe_donate_sc tcbptr ntfnptr
   \<lbrace>\<lambda>rv s. active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> released_sc_tcb_at tcbptr s\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_cond_released_sc_tcb_at refill_unblock_check_ko_at_SchedContext
                     sched_context_donate_sc_tcb_sc_at sched_context_donate_bound_sc_tcb_at
                simp: get_sc_obj_ref_def)
  apply (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)
  apply wpsimp
  apply (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)
  done

lemma maybe_donate_sc_cond_released_if_bound_sc_tcb_at:
  "\<lbrace>released_if_bound_sc_tcb_at tcbptr and st_tcb_at runnable tcbptr\<rbrace>
   maybe_donate_sc tcbptr ntfnptr
   \<lbrace>\<lambda>rv s. active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s
            \<longrightarrow> released_if_bound_sc_tcb_at tcbptr s\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule maybe_donate_sc_cond_released_sc_tcb_at)
  by simp

lemma maybe_donate_sc_active_sc_valid_refills[wp]:
  "\<lbrace>active_sc_valid_refills
    and current_time_bounded 1
    and valid_machine_time\<rbrace>
   maybe_donate_sc tcbptr ntfnptr
   \<lbrace>\<lambda>rv s. active_sc_valid_refills s\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: refill_unblock_check_active_sc_valid_refills hoare_drop_imp
                 hoare_vcg_if_lift2)

crunches test_reschedule
  for ready_or_release[wp]: "ready_or_release"

lemma postpone_ready_or_release[wp]:
  "\<lbrace>valid_ready_qs and ready_or_release\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  unfolding postpone_def get_sc_obj_ref_def
  by (wpsimp wp: tcb_dequeue_not_queued)+

lemma sched_context_resume_ready_or_release[wp]:
  "\<lbrace>valid_ready_qs and ready_or_release\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift hoare_vcg_if_lift simp: is_schedulable_def)

lemma maybe_donate_sc_ready_or_release[wp]:
  "\<lbrace>valid_ready_qs and valid_machine_time and active_sc_valid_refills
    and ready_or_release and not_queued tcb_ptr and scheduler_act_not tcb_ptr\<rbrace>
   maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  unfolding maybe_donate_sc_def when_def maybeM_def
  by (wpsimp wp: sched_context_donate_valid_ready_qs' get_sc_obj_ref_wp get_sk_obj_ref_wp
                 get_tcb_obj_ref_wp)

crunches maybe_donate_sc
  for tcb_at[wp]: "tcb_at p"
  (wp: crunch_wps)

context DetSchedSchedule_AI begin

lemma maybe_donate_sc_active_reply_scs[wp]:
  "maybe_donate_sc t n \<lbrace>active_reply_scs\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma send_signal_WaitingNtfn_helper:
  notes not_not_in_eq_in[iff] shows
  "ntfn_obj ntfn = WaitingNtfn wnlist \<Longrightarrow>
   \<lbrace>ko_at (Notification ntfn) ntfnptr and
    st_tcb_at ((=) (BlockedOnNotification ntfnptr)) (hd wnlist) and
    valid_sched and invs and
    current_time_bounded 1\<rbrace>
   update_waiting_ntfn ntfnptr wnlist (ntfn_bound_tcb ntfn) (ntfn_sc ntfn) badge
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wpsimp)
           apply (wpsimp wp: possible_switch_to_valid_sched_strong)
          apply (wpsimp wp: is_schedulable_wp)+
        apply (rename_tac tcbptr x)
        apply (rule_tac Q="\<lambda>r s. tcbptr \<noteq> idle_thread s \<and> pred_map runnable (tcb_sts_of s) tcbptr \<and>
                                 valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s \<and>
        (active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s \<longrightarrow> released_sc_tcb_at tcbptr s)"
        in hoare_strengthen_post[rotated])
         apply (clarsimp simp: obj_at_def valid_sched_def
                        split: option.splits dest!: get_tcb_SomeD)
         apply (intro conjI; intro allI impI)
          apply (intro conjI; intro allI impI)
           apply (clarsimp simp: not_in_release_q_def pred_map_eq_def is_schedulable_bool_def2)
          apply (erule valid_blocked_divided_threadE)
          apply (clarsimp simp: valid_blocked_thread_def tcb_at_kh_simps is_schedulable_bool_def2)
         apply (subgoal_tac "valid_blocked s", clarsimp)
         apply (erule valid_blocked_divided_threadE)
         apply (clarsimp simp: valid_blocked_thread_def vs_all_heap_simps)
        apply (wpsimp wp: maybe_donate_sc_valid_ready_qs maybe_donate_sc_valid_release_q
                          maybe_donate_sc_valid_sched_action
                          maybe_donate_sc_ct_in_cur_domain maybe_donate_sc_valid_blocked_except_set
                          maybe_donate_sc_released_ipc_queues maybe_donate_sc_cond_released_sc_tcb_at
                     simp: valid_sched_def)
       apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
      apply (rule_tac Q="\<lambda>_ s. (valid_sched_except_blocked s \<and> valid_blocked_except_set {x1} s)
                         \<and> not_queued x1 s \<and>
                  x1 \<noteq> idle_thread s \<and>
                  sym_refs (state_refs_of s) \<and>
                  valid_objs s \<and> current_time_bounded 1 s \<and>
                   pred_map runnable (tcb_sts_of s) x1 \<and> valid_machine_time s \<and> scheduler_act_not x1 s \<and> not_in_release_q x1 s \<and>
                  released_if_bound_sc_tcb_at x1 s"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp simp: valid_sched_def tcb_at_kh_simps pred_map_def)
       apply (case_tac y; simp)
      apply (rule hoare_vcg_conj_lift)
       apply (rule set_thread_state_break_valid_sched[simplified pred_conj_def])
      apply (wpsimp wp: set_thread_state_pred_map_tcb_sts_of)
     apply simp
     apply wpsimp
    apply wpsimp
   apply (wpsimp wp: assert_inv)
  apply (clarsimp simp: valid_sched_def)
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
  apply (intro conjI)
          apply (erule valid_ready_qs_not_queued_not_runnable, clarsimp simp: tcb_at_kh_simps pred_map_def)
         apply (fastforce dest: st_tcb_at_idle_thread)
        defer
        apply (clarsimp simp: not_cur_thread_def ct_in_state_def tcb_at_kh_simps pred_map_def)
      subgoal for s
      apply (subgoal_tac "valid_ntfn ntfn s")
       apply (clarsimp simp: valid_ntfn_def split: list.splits option.splits)
       apply (case_tac wnlist; simp)
      by (frule invs_valid_objs, fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def)
     apply (rule valid_sched_not_runnable_scheduler_act_not; clarsimp simp: valid_sched_def tcb_at_kh_simps pred_map_def)
    apply (rule valid_sched_not_runnable_not_in_release_q; clarsimp simp: valid_sched_def tcb_at_kh_simps pred_map_def)
    subgoal for s
      apply (prop_tac "ipc_queued_thread (hd wnlist) s", simp add: tcb_at_kh_simps pred_map_def)
      apply (rule released_ipc_queues_blocked_on_recv_ntfn_D, simp)
      by (fastforce elim: pred_map_weakenE simp: tcb_at_kh_simps is_blocked_thread_state_defs)
    (* sym_refs *) (* FIXME: this is nasty, can it be improved? *)
    apply (case_tac wnlist; clarsimp)
    apply (rule delta_sym_refs[OF invs_sym_refs], assumption)
     apply (clarsimp split: if_splits)
     apply (intro conjI; intro impI;
            fastforce simp: obj_at_def state_refs_of_def get_refs_def2 ntfn_q_refs_of_def
                     dest!: symreftype_inverse'
                     split: option.splits list.splits)
    apply (frule invs_valid_objs)
    apply (drule (1) valid_objs_ko_at, clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (clarsimp split: if_splits simp: pred_tcb_at_def obj_at_def)
     apply (intro conjI impI;
            clarsimp simp: tcb_st_refs_of_def state_refs_of_def
                     split: option.splits if_splits list.splits thread_state.splits
                     dest!: symreftype_inverse')
              apply (clarsimp simp: get_refs_def2)+
    by (intro conjI impI;
        fastforce simp: is_tcb obj_at_def state_refs_of_def get_refs_def2 ntfn_q_refs_of_def
                  dest!: symreftype_inverse'
                  split: option.splits list.splits if_splits)

declare sts_st_tcb_at' [wp]

lemma cancel_signal_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at (Not \<circ> runnable) tcbptr\<rbrace>
      cancel_signal tcbptr ntfnptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding cancel_signal_def
  apply (wpsimp wp: set_thread_state_valid_sched
                    set_object_wp get_simple_ko_wp)
  apply (strengthen valid_sched_not_runnable_scheduler_act_not
                    valid_sched_not_runnable_not_in_release_q
                    valid_sched_not_runnable_not_queued)
  by (clarsimp simp: valid_sched_def tcb_at_kh_simps pred_map_def)

lemma blocked_cancel_ipc_BOR_valid_sched':
  "\<lbrace>valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r pl) tcbptr r
   \<lbrace>\<lambda>rv s. valid_sched (s :: ('state_ext state))\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def get_blocking_object_def thread_get_def
                  wp: set_thread_state_valid_sched
                      reply_unlink_tcb_valid_sched get_simple_ko_wp)
           apply (rule_tac Q="\<lambda>r s. valid_sched s \<and> scheduler_act_not tcbptr s
                                    \<and> st_tcb_at (\<lambda>ts. \<not> runnable ts) tcbptr s"
                        in hoare_strengthen_post[rotated])
            apply (clarsimp simp: valid_sched_def)
            apply (intro conjI)
             apply (erule valid_ready_qs_not_queued_not_runnable)
             apply (clarsimp simp: st_tcb_at_def obj_at_def)
            apply (erule valid_release_q_not_in_release_q_not_runnable)
            apply (simp add: vs_all_heap_simps obj_at_kh_kheap_simps)
           apply (wpsimp simp: get_blocking_object_def
                           wp: get_simple_ko_wp reply_unlink_tcb_valid_sched)+
        apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_drop_imp set_object_wp
                    simp: set_simple_ko_def get_blocking_object_def)+
  apply (clarsimp simp: scheduler_act_not_def valid_sched_def valid_sched_action_def
                        weak_valid_sched_action_2_def st_tcb_at_def obj_at_def)
  apply (intro conjI impI)
     apply (erule valid_ready_qs_not_queued_not_runnable)
     apply (clarsimp simp: st_tcb_at_def obj_at_def)
    apply (erule valid_release_q_not_in_release_q_not_runnable)
    apply (simp add: vs_all_heap_simps obj_at_kh_kheap_simps)
   apply (clarsimp simp: scheduler_act_not_def valid_sched_def valid_sched_action_def
                         weak_valid_sched_action_2_def st_tcb_at_def obj_at_def vs_all_heap_simps)+
  done

lemma blocked_cancel_ipc_BOR_st_tcb_at_not_runnable[wp]:
  "\<lbrace>tcb_at tcbptr\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r pl) tcbptr r
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

lemma cancel_ipc_valid_sched_misc[wp]:
  "cancel_ipc t
   \<lbrace>\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s)
                            (idle_thread s) (ready_queues s) (release_queue s) (last_machine_time_of s)
                            (etcbs_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)\<rbrace>"
  by (wpsimp wp: gts_wp' simp: cancel_ipc_def)

end

lemma sts_cancel_ipc_Running_invs:
  "\<lbrace>st_tcb_at ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState) t
        and invs and ex_nonz_cap_to t and fault_tcb_at ((=) None) t\<rbrace>
    set_thread_state t Running
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wp sts_invs_minor2)
  apply clarsimp
  apply (auto elim!: pred_tcb_weakenE
           notE [rotated, OF _ idle_no_ex_cap]
           simp: invs_def valid_state_def valid_pspace_def)
  done

lemma cancel_ipc_invs_st_tcb_at:
  "\<lbrace>invs\<rbrace> cancel_ipc t
   \<lbrace>\<lambda>rv. invs and st_tcb_at ((=) Running or (=) Inactive or (=) Restart or
                             (=) IdleThreadState) t
              and fault_tcb_at ((=) None) t\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: cancel_ipc_simple_except_awaiting_reply)

lemma set_thread_state_running_not_ipc_queued_thread:
  "\<lbrace> \<top> \<rbrace>
   set_thread_state tcbptr Running
   \<lbrace>\<lambda>_. not_ipc_queued_thread tcbptr\<rbrace>"
  by (wpsimp simp: vs_all_heap_simps set_thread_state_def wp: set_object_wp)

lemma set_thread_state_pred_map_eq[wp]:
  "\<lbrace>\<top>\<rbrace> set_thread_state t st \<lbrace>\<lambda>_ s. pred_map_eq st (tcb_sts_of s) t\<rbrace>"
  by (wpsimp wp: valid_sched_wp simp: vs_all_heap_simps)

context DetSchedSchedule_AI begin

lemma send_signal_BOR_helper:
  notes not_not_in_eq_in[iff] shows
  "ntfn_obj ntfn = IdleNtfn
   \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr
   \<Longrightarrow> \<lbrace>st_tcb_at ((=) (BlockedOnReceive ep r_opt pl)) tcbptr and
        valid_sched and (\<lambda>s. tcbptr \<noteq> idle_thread s) and invs
        and current_time_bounded 1\<rbrace>
         do y <- cancel_ipc tcbptr;
            y <- set_thread_state tcbptr Running;
            y <- as_user tcbptr (setRegister badge_register badge);
            y <- maybe_donate_sc tcbptr ntfnptr;
            in_release_q <- gets (in_release_queue tcbptr);
            schedulable <- is_schedulable tcbptr in_release_q;
            when schedulable (possible_switch_to tcbptr)
         od
       \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule_tac B="\<lambda>_. released_if_bound_sc_tcb_at tcbptr
                          and scheduler_act_not tcbptr
                          and not_queued tcbptr
                          and not_in_release_q tcbptr
                          and valid_sched
                          and (\<lambda>s. tcbptr \<noteq> idle_thread s)
                          and st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = {}) tcbptr
                          and invs
                          and current_time_bounded 1"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_ex_lift cancel_ipc_no_refs)
   apply (clarsimp simp: valid_sched_def invs_sym_refs invs_valid_objs)
   apply (intro conjI)
      apply (rule released_ipc_queues_blocked_on_recv_ntfn_D, simp)
      apply (fastforce elim: pred_map_weakenE simp: tcb_at_kh_simps is_blocked_thread_state_defs)
     apply (rule weak_valid_sched_action_scheduler_action_not)
      apply (erule valid_sched_action_weak_valid_sched_action)
     apply (simp add: pred_tcb_at_def obj_at_def)
     using runnable.simps apply metis
    apply (erule valid_ready_qs_not_queued_not_runnable)
    apply (simp add: pred_tcb_at_def obj_at_def)
    using runnable.simps apply metis
   apply (erule valid_release_q_not_in_release_q_not_runnable)
   apply (simp add: pred_tcb_at_def obj_at_def)
   using runnable.simps apply metis
  apply (rule_tac B="\<lambda>_. released_if_bound_sc_tcb_at tcbptr
                          and scheduler_act_not tcbptr
                          and not_queued tcbptr
                          and not_in_release_q tcbptr
                          and valid_sched_except_blocked
                          and valid_blocked_except tcbptr
                          and (\<lambda>s. tcbptr \<noteq> idle_thread s)
                          and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))
                          and (\<lambda>s. pred_map_eq Running (tcb_sts_of s) tcbptr)
                          and current_time_bounded 1"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_thread_state_runnable_valid_sched_except_blocked
                     set_thread_state_valid_blocked)
   apply (clarsimp simp: valid_sched_def invs_valid_objs obj_at_kh_kheap_simps vs_all_heap_simps
                         tcb_non_st_state_refs_of_state_refs_of[rotated] if_fun_simp)
  apply (wpsimp wp: possible_switch_to_valid_sched_strong)
      apply (wpsimp wp: is_schedulable_wp')+
    apply (rule_tac Q="\<lambda>r s. tcbptr \<noteq> idle_thread s \<and> st_tcb_at runnable tcbptr s
                             \<and> valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s
                             \<and> (active_sc_tcb_at tcbptr s \<longrightarrow> not_in_release_q tcbptr s
                                \<longrightarrow> released_if_bound_sc_tcb_at tcbptr s)"
                 in hoare_strengthen_post[rotated])
     apply (clarsimp simp: obj_at_def valid_sched_def split: option.splits
                    dest!: get_tcb_SomeD)
     apply (clarsimp dest!: schedulable_unfold2 st_tcb_at_tcb_at)
     apply (intro conjI allI impI)
       apply (clarsimp simp: not_in_release_q_def vs_all_heap_simps obj_at_kh_kheap_simps
                             pred_tcb_at_def obj_at_def)
      apply (erule valid_blocked_divided_threadE)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                            vs_all_heap_simps obj_at_kh_kheap_simps runnable_eq_active
                            valid_blocked_defs)
     apply (erule valid_blocked_divided_threadE)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
                           vs_all_heap_simps obj_at_kh_kheap_simps runnable_eq_active
                           valid_blocked_defs)
    apply (wpsimp wp: maybe_donate_sc_valid_ready_qs maybe_donate_sc_valid_release_q
                      maybe_donate_sc_valid_sched_action
                      maybe_donate_sc_ct_in_cur_domain maybe_donate_sc_valid_blocked_except_set
                      maybe_donate_sc_cond_released_if_bound_sc_tcb_at
                      maybe_donate_sc_released_ipc_queues'
                simp: valid_sched_def)
   apply (wpsimp cong: conj_cong simp: obj_at_kh_kheap_simps)
  apply (clarsimp simp: valid_sched_def obj_at_kh_kheap_simps vs_all_heap_simps current_time_bounded_def)
  done

(* what can we say about ntfn_bound_tcb? can we say it is not equal to idle_thread or cur_thread? *)
lemma send_signal_valid_sched:
  "\<lbrace> valid_sched and invs
     and current_time_bounded 1\<rbrace>
     send_signal ntfnptr badge
   \<lbrace> \<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_signal_def
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (case_tac "ntfn_bound_tcb ntfn"; clarsimp)
     apply wpsimp
    apply (rule hoare_seq_ext[OF _ gts_sp])
    apply (case_tac st; clarsimp simp: receive_blocked_def)
           prefer 4
           apply (rename_tac ep r_opt pl)
           apply (rule hoare_weaken_pre)
           apply (rule_tac ep = ep and r_opt = r_opt in send_signal_BOR_helper; simp)
           apply (clarsimp simp: pred_conj_def pred_tcb_at_def pred_tcb_at_eq_commute obj_at_def
                          split: option.splits)
           apply (drule invs_valid_idle, clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
           apply fastforce
          prefer 8
           apply (rename_tac queue)
          apply (wpsimp wp: send_signal_WaitingNtfn_helper)
          apply (subgoal_tac "queue \<noteq> [] \<and> tcb_at (hd queue) s")
             apply (subgoal_tac "(ntfnptr, TCBSignal) \<in> state_refs_of s (hd queue)")
              apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_refs_of_rev(4)[symmetric] obj_at_def
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

lemma receive_ipc_preamble_valid_sched:
  "\<lbrace>valid_sched and invs\<rbrace>
    receive_ipc_preamble reply_cap thread
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: receive_ipc_preamble_def invs_valid_objs
               wp: cancel_ipc_valid_sched weak_if_wp get_sk_obj_ref_inv)

(* FIXME: Move to Finalise_AI *)
lemma cancel_ipc_st_tcb_at_not_blocked:
  assumes "\<And>r. \<not> P (P' (BlockedOnReply r))"
  assumes "\<And>ep r pl. \<not> P (P' (BlockedOnReceive ep r pl))"
  assumes "\<And>ep data. \<not> P (P' (BlockedOnSend ep data))"
  assumes "\<And>ntfn. \<not> P (P' (BlockedOnNotification ntfn))"
  shows "cancel_ipc t \<lbrace>\<lambda>s. P (st_tcb_at P' t' s)\<rbrace>"
  apply (wpsimp wp: cancel_ipc_st_tcb_at)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  by (case_tac "tcb_state tcb"; clarsimp simp: assms)

(* FIXME: Move to Finalise_AI *)
lemmas cancel_ipc_st_tcb_at_active
  = cancel_ipc_st_tcb_at_not_blocked[of id active, simplified]

(* FIXME: move to IpcDet_AI *)
lemma receive_ipc_preamble_lift:
  assumes "\<And>t. cancel_ipc t \<lbrace>P\<rbrace>"
  shows "receive_ipc_preamble reply_cap thread \<lbrace>P\<rbrace>"
  by (wpsimp simp: receive_ipc_preamble_def wp: assms)

crunches receive_ipc_preamble
  for cur_thread[wp]: "(\<lambda>s. P (cur_thread s))"
  and not_queued[wp]: "not_queued thread "
  and not_in_release_q[wp]: "not_in_release_q thread"
  and scheduler_act_not[wp]: "scheduler_act_not thread"
  (wp: hoare_drop_imps)

crunches receive_ipc_preamble
  for released_if_bound[wp]: "released_if_bound_sc_tcb_at t"
  (ignore: thread_set update_sched_context wp: crunch_wps)

crunches complete_signal, do_nbrecv_failed_transfer
  for valid_sched[wp]: "valid_sched"

(* Preconditions for the guts of receive_ipc, after the reply preamble *)
abbreviation (input) receive_ipc_valid_sched_preconds ::
  "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cap \<Rightarrow> obj_ref option \<Rightarrow> endpoint \<Rightarrow> ('state_ext state \<Rightarrow> bool) \<Rightarrow> 'state_ext state \<Rightarrow> bool"
  where
  "receive_ipc_valid_sched_preconds t ep_ptr reply reply_opt ep ex_invs \<equiv>
    \<lambda>s. valid_sched s
         \<and> st_tcb_at active t s
         \<and> cur_thread s = t
         \<and> not_queued t s
         \<and> not_in_release_q t s
         \<and> scheduler_act_not t s
         \<and> released_if_bound_sc_tcb_at t s
         \<and> receive_ipc_preamble_rv reply reply_opt s
         \<and> ko_at (Endpoint ep) ep_ptr s
         \<and> ex_invs s"

lemma receive_ipc_blocked_valid_sched':
  assumes ep: "case ep of IdleEP \<Rightarrow> queue = [] | RecvEP q \<Rightarrow> queue = q | SendEP _ \<Rightarrow> False"
  shows "\<lbrace> receive_ipc_valid_sched_preconds t ep_ptr reply reply_opt ep invs \<rbrace>
          receive_ipc_blocked is_blocking t ep_ptr reply_opt pl queue
         \<lbrace> \<lambda>rv. valid_sched \<rbrace>"
  apply (cases reply_opt; clarsimp simp: receive_ipc_blocked_def)
   apply (wpsimp wp: set_thread_state_valid_sched)
   apply (clarsimp simp: valid_sched_def)
  apply (wpsimp wp: set_thread_state_valid_sched)
  apply (clarsimp simp: valid_sched_def)
  done

lemma receive_ipc_idle_valid_sched:
  "\<lbrace> receive_ipc_valid_sched_preconds t ep_ptr reply reply_opt IdleEP invs \<rbrace>
    receive_ipc_idle is_blocking t ep_ptr reply_opt pl
   \<lbrace> \<lambda>rv. valid_sched \<rbrace>"
  apply (rule hoare_weaken_pre, rule monadic_rewrite_refine_valid[where P''=\<top>])
  apply (rule monadic_rewrite_receive_ipc_idle)
  apply (rule receive_ipc_blocked_valid_sched'[where ep=IdleEP and reply=reply])
  by (auto simp: st_tcb_at_tcb_at)

lemmas receive_ipc_blocked_valid_sched =
  receive_ipc_blocked_valid_sched'[where ep="RecvEP queue" and queue=queue for queue, simplified]
  receive_ipc_idle_valid_sched

lemma receive_ipc_valid_sched:
  "\<lbrace>\<lambda>s. valid_sched s
        \<and> st_tcb_at active thread s
        \<and> thread = cur_thread s
        \<and> not_queued thread s
        \<and> not_in_release_q thread s
        \<and> scheduler_act_not thread s
        \<and> released_if_bound_sc_tcb_at thread s
        \<and> invs s\<rbrace>
    receive_ipc thread ep_cap is_blocking reply_cap
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  supply if_split[split del]
  apply (cases ep_cap
         ; simp add: receive_ipc_def split_def receive_ipc_preamble_def[symmetric]
                     receive_ipc_blocked_def[symmetric] receive_ipc_idle_def[symmetric]
               cong: endpoint.case_cong bool.case_cong)
  apply (rename_tac ep_ptr ep_badge ep_rights)
  apply (rule hoare_seq_ext[where B="\<lambda>rv s. receive_ipc_preamble_rv reply_cap rv s \<and> ?pre s", rotated]
         , wpsimp wp: receive_ipc_preamble_valid_sched receive_ipc_preamble_st_tcb_at
                      ct_in_state_thread_state_lift receive_ipc_preamble_invs
                      receive_ipc_preamble_lift[OF cancel_ipc_st_tcb_at_active]
                      receive_ipc_preamble_rv)
  apply (rename_tac reply_opt)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ gbn_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ get_notification_default_sp])
  apply (rule hoare_weaken_pre)
   apply (rule_tac R="receive_ipc_valid_sched_preconds thread ep_ptr reply_cap reply_opt ep invs"
            in hoare_vcg_if_split, wp)
   prefer 2 apply fastforce
  apply (thin_tac "\<not> (_ \<and> _)", clarsimp)
  \<comment> \<open>IdleEP, RecvEP\<close>
  apply (case_tac ep; clarsimp simp: receive_ipc_blocked_valid_sched[where reply=reply_cap])
  \<comment> \<open>SendEP\<close>
  apply (rename_tac queue)
  apply (rule hoare_seq_ext[OF _ assert_sp], simp)
  apply (rule_tac S="ep_ptr \<notin> set queue \<and> distinct queue" in hoare_gen_asm'')
   apply (clarsimp simp: obj_at_def)
   apply (erule (1) pspace_valid_objsE[OF _ invs_valid_objs])
   apply (clarsimp simp: valid_obj_def valid_ep_def)
   apply (drule (1) bspec)
   apply (clarsimp simp: obj_at_def is_tcb)
  apply (case_tac queue; clarsimp cong: if_cong list.case_cong)
  apply (rename_tac sender queue)
  apply (rule_tac s="mk_ep SendEP queue" in subst[where P="\<lambda>c. \<lbrace>P\<rbrace> set_endpoint p c >>= r \<lbrace>Q\<rbrace>" for P p r Q]
         , simp add: mk_ep_def split: list.splits)
  apply (rule_tac B="\<lambda>r. receive_ipc_valid_sched_preconds thread ep_ptr reply_cap reply_opt
                           (mk_ep SendEP queue)
                           (\<lambda>s. sym_refs (\<lambda>p. if p = ep_ptr then set (sender # queue) \<times> {EPSend}
                                                            else state_refs_of s p)
                                \<and> all_invs_but_sym_refs s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_ball_lift set_simple_ko_at valid_ioports_lift)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (apply_conjunct \<open>erule delta_sym_refs; fastforce simp: ko_at_state_refs_ofD
                                                         split: if_splits\<close>)
   apply (fastforce elim!: obj_at_valid_objsE if_live_then_nonz_capD2
                     simp: valid_obj_def valid_ep_def mk_ep_def live_def
                    split: endpoint.splits if_splits)
  \<comment> \<open>get_thread_state\<close>
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac sender_state; clarsimp)
  apply (rename_tac ep_ptr' sender_data)
  \<comment> \<open>do_ipc_transfer, and stash some knowledge for later\<close>
  apply (rule_tac B="\<lambda>r. receive_ipc_valid_sched_preconds thread ep_ptr reply_cap reply_opt
                           (mk_ep SendEP queue)
                           (\<lambda>s. st_tcb_at ((=) (BlockedOnSend ep_ptr sender_data)) sender s
                                \<and> state_refs_of s ep_ptr = set queue \<times> {EPSend}
                                \<and> all_invs_but_sym_refs s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp simp: st_tcb_at_tcb_at)
   apply (rule_tac V="ep_ptr' = ep_ptr" in revcut_rl
          , (drule_tac x=ep_ptr and y=sender and tp=TCBBlockedSend in sym_refsE
             ; fastforce simp: in_state_refs_of_iff refs_of_rev pred_tcb_at_def obj_at_def)
          , clarsimp)
   apply (frule ko_at_state_refs_ofD, simp)
  \<comment> \<open>thread_get tcb_fault\<close>
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_if[rotated])
   \<comment> \<open>if not call and no fault: sender \<rightarrow> Running\<close>
   apply (wpsimp wp: set_thread_state_possible_switch_to_valid_sched)
   apply (intro conjI)
    apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise)
    apply (frule valid_sched_released_ipc_queues, drule_tac t=sender in released_ipc_queues_blocked_on_send_E1)
     apply (clarsimp elim!: pred_map_eq_pred_mapE)
    apply (fastforce simp: vs_all_heap_simps is_timeout_fault_opt_def)
   apply (erule (1) not_idle_thread', clarsimp)
  apply (rule hoare_if[rotated])
   \<comment> \<open>if not grant or no reply: sender \<longrightarrow> Inactive\<close>
   apply (wpsimp wp: set_thread_state_Inactive_not_queued_valid_sched cong: if_cong)
   apply (intro conjI;
          clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def
                 intro!: valid_sched_valid_blocked
                         valid_sched_imp_except_blocked
                         valid_sched_scheduler_act_not_better
                  elim!: valid_ready_qs_not_queued_not_runnable[OF valid_sched_valid_ready_qs]
                         valid_release_q_not_in_release_q_not_runnable[OF valid_sched_valid_release_q])
  \<comment> \<open>otherwise (grant and reply and (call or fault)): reply_push\<close>
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: reply_push_valid_sched)
  apply (clarsimp simp: valid_sched_valid_sched_except_blocked[THEN iffD1]
                        obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (prop_tac "\<not> pred_map runnable (tcb_sts_of s) sender", clarsimp simp: vs_all_heap_simps)
  apply (clarsimp simp: valid_sched_not_runnable_scheduler_act_not
                        valid_sched_not_runnable_not_queued
                        valid_sched_not_runnable_not_in_release_q)
  apply (prop_tac "active_if_bound_sc_tcb_at sender s")
   apply (frule valid_sched_released_ipc_queues, drule_tac t=sender in released_ipc_queues_blocked_on_send_E1
          ; fastforce simp: vs_all_heap_simps)
  apply simp
  by (match premises in H: \<open>ct_in_state' active s\<close> for s \<Rightarrow> \<open>insert H, fastforce simp: vs_all_heap_simps\<close>)

end

crunches schedule_tcb
  for valid_sched[wp]: valid_sched
  (wp: reschedule_valid_sched_const)

crunches maybe_return_sc
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: wp: hoare_drop_imp hoare_vcg_if_lift2 ignore: set_tcb_obj_ref)

(* FIXME: move somewhere appropriate *)
lemma tcb_sc_refill_cfgs_upd:
  "tcb_sc_refill_cfgs_2 (\<lambda>a. if a = tptr then Some None else tcb_scps_of s a) (sc_refill_cfgs_of s)
   = (\<lambda>a. if a = tptr then None else tcb_sc_refill_cfgs_2 (tcb_scps_of s) (sc_refill_cfgs_of s) a)"
  unfolding tcb_sc_refill_cfgs_2_def
  by (fastforce simp: map_join_def vs_all_heap_simps opt_map_def)

(* FIXME: move somewhere appropriate *)
lemma sc_ready_times_upd:
  "sc_ready_times_2 (\<lambda>a. if a = tptr then None else tcb_sc_refill_cfgs_of s a)
   = (\<lambda>a. if a = tptr then None else sc_ready_times_2 (tcb_sc_refill_cfgs_of s) a)"
  unfolding sc_ready_times_2_def
  by (clarsimp simp: map_project_upd)

(* FIXME: move somewhere appropriate, maybe rename *)
lemma sorted_release_q_heap_upd_idem:
  "not_in_release_q tptr s \<Longrightarrow>
   sorted_release_q_2 (\<lambda>a. if a = tptr then None else tcb_sc_refill_cfgs_of s a) (release_queue s)
   = sorted_release_q_2 (tcb_sc_refill_cfgs_of s) (release_queue s)"
  by (rule sorted_release_q_2_eq_lift, clarsimp simp: in_release_q_def sc_ready_times_upd)

lemma maybe_return_sc_valid_sched[wp]:
  "\<lbrace> valid_sched and scheduler_act_not tptr and not_queued tptr and not_in_release_q tptr\<rbrace>
   maybe_return_sc ntfnptr tptr
   \<lbrace> \<lambda>_. valid_sched\<rbrace>"
  apply (simp add: maybe_return_sc_def assert_opt_def)
  apply (wpsimp wp: valid_sched_wp get_tcb_obj_ref_wp get_sk_obj_ref_wp)
  apply (clarsimp simp: valid_sched_def)
  apply (intro conjI)
      apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps not_queued_def)
     apply (clarsimp simp: valid_release_q_def vs_all_heap_simps not_in_release_q_def)
     apply (intro conjI)
      apply clarsimp
     apply (clarsimp simp: tcb_sc_refill_cfgs_upd
            , subst sorted_release_q_heap_upd_idem
            , clarsimp simp: not_in_release_q_def
            , simp)
    apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def vs_all_heap_simps
                          scheduler_act_not_def)
   apply (clarsimp simp: valid_blocked_defs vs_all_heap_simps)
  apply (clarsimp simp: released_ipc_queues_defs vs_all_heap_simps)
  done

crunches do_nbrecv_failed_transfer
for valid_sched[wp]: valid_sched

lemma as_user_is_sc_active[wp]:
  "\<lbrace>is_sc_active scp\<rbrace> as_user tptr f \<lbrace>\<lambda>_. is_sc_active scp\<rbrace>"
  apply (wpsimp simp: as_user_def wp: set_object_wp)
  by (clarsimp simp: is_sc_active_def dest!: get_tcb_SomeD split: option.splits)

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

lemma maybe_donate_sc_valid_blocked:
  "\<lbrace>valid_blocked and not_queued tcb_ptr and scheduler_act_not tcb_ptr
    and (\<lambda>s. tcb_ptr = cur_thread s)\<rbrace>
   maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  by (wpsimp wp: sched_context_donate_valid_blocked
                 get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma maybe_donate_sc_active_reply_scs:
  "maybe_donate_sc tcb_ptr ntfnptr \<lbrace>active_reply_scs\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  by (wpsimp wp: get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma maybe_donate_sc_valid_sched:
  "\<lbrace>valid_sched and valid_objs and (\<lambda>s. sym_refs (state_refs_of s)) and not_queued tcb_ptr
    and scheduler_act_not tcb_ptr and current_time_bounded 1
    and not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr
    and (\<lambda>s. tcb_ptr = cur_thread s)\<rbrace>
   maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: maybe_donate_sc_valid_ready_qs maybe_donate_sc_valid_release_q
                 maybe_donate_sc_valid_sched_action
                 maybe_donate_sc_ct_in_cur_domain maybe_donate_sc_valid_blocked
                 maybe_donate_sc_released_ipc_queues'
                 maybe_donate_sc_active_reply_scs
           simp: valid_sched_def tcb_at_kh_simps vs_all_heap_simps
                 ipc_queued_thread_state_not_runnable)

lemmas as_user_bound_tcb[wp] = as_user_bound_obj_typ_at[where T=ATCB, folded tcb_at_typ]

lemma receive_signal_valid_sched:
  "\<lbrace>valid_sched and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))
    and current_time_bounded 1 and scheduler_act_not thread and not_queued thread
    and not_in_release_q thread and (\<lambda>s. thread = cur_thread s)
    and released_if_bound_sc_tcb_at thread and st_tcb_at runnable thread\<rbrace>
   receive_signal thread cap is_blocking
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: receive_signal_def)
  apply (cases cap; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (wpsimp wp: set_thread_state_valid_sched)
    apply (clarsimp simp: valid_sched_def)
   apply (wpsimp wp: set_thread_state_valid_sched)
   apply (clarsimp simp: valid_sched_def)
  apply (wpsimp wp: maybe_donate_sc_valid_sched simp: valid_ntfn_def)
  apply (drule(1) valid_objs_ko_at)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule delta_sym_refs)
   apply (auto simp: ko_at_state_refs_ofD dest: delta_sym_refs split: if_splits)
  done

(*
crunch valid_sched: schedule_tcb,maybe_return_sc,maybe_donate_sc valid_sched
  (wp: set_thread_state_Inactive_simple_sched_action_not_runnable maybeM_inv)

crunch valid_sched: receive_signal valid_sched
  (wp: set_thread_state_Inactive_simple_sched_action_not_runnable maybeM_inv mapM_wp)
*)

crunches restart_thread_if_no_fault
  for not_queued[wp]: "not_queued t"
  (wp: crunch_wps)

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
         | wpc | wp (once) hoare_vcg_all_lift)+
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
      | wpc | wp (once) hoare_vcg_all_lift)+
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
  apply (wpsimp simp: update_sk_obj_ref_def sched_context_maybe_unbind_ntfn_def get_sk_obj_ref_def
                  wp: get_simple_ko_wp get_sched_context_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI, clarsimp)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def valid_bound_obj_def obj_at_def
                  dest!: is_sc_objD)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (fastforce dest: refs_in_ntfn_q_refs refs_in_get_refs
                    simp: state_refs_of_def valid_ntfn_def obj_at_def is_sc_obj_def
                   split: if_split_asm option.split_asm ntfn.splits kernel_object.split_asm)[1]
  apply (clarsimp split: if_splits)
   apply (fastforce simp: obj_at_def
                       dest!: refs_in_get_refs SCNtfn_in_state_refsD ntfn_sc_sym_refsD)
  apply (clarsimp simp: state_refs_of_def)
  done

lemma sched_context_unbind_tcb_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_unbind_tcb scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def
      wp: tcb_dequeue_not_queued_gen reschedule_required_not_queued get_sched_context_wp)

lemma sched_context_unbind_all_tcbs_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_unbind_all_tcbs scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def wp: get_sched_context_wp)

lemma fast_finalise_not_queued:
  "\<lbrace>valid_objs and sym_refs \<circ> state_refs_of and st_tcb_at active t and scheduler_act_not t
    and not_queued t\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (cases cap; simp)
      apply wpsimp
     apply (wpsimp wp: cancel_all_ipc_not_queued)
    apply (wpsimp wp: cancel_all_signals_not_queued unbind_maybe_notification_valid_objs)
   apply (wpsimp wp: gts_wp get_simple_ko_wp)
  apply wpsimp
  done

lemma cap_insert_check_cap_ext_valid[wp]:"
  \<lbrace>valid_list\<rbrace>
   check_cap_at new_cap src_slot (check_cap_at t slot (cap_insert new_cap src_slot x))
  \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (wp get_cap_wp | simp)+
  done

crunches lookup_cap, lookup_reply
  for valid_sched[wp]: "valid_sched_pred P"
  and ct_in_state[wp]: "ct_in_state P"

context DetSchedSchedule_AI begin

lemma budget_sufficient_bound_sc:
  "budget_sufficient t s \<Longrightarrow> bound_sc_tcb_at bound t s"
  by (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)

lemma st_tcb_at_strengthen_pred:
  "st_tcb_at P t s \<Longrightarrow> (\<forall>st. P st \<longrightarrow> Q st) \<Longrightarrow> st_tcb_at Q t s"
  by (clarsimp simp: tcb_at_kh_simps ct_in_state_def vs_all_heap_simps runnable_eq)

(* FIXME RT: move *)
lemma is_timeout_fault_simp[simp]:
  "is_timeout_fault (CapFault ref b f) = False"
  by (clarsimp simp: is_timeout_fault_def)

lemma lookup_reply_not_timeout[wp]:
  "\<lbrace>invs\<rbrace> lookup_reply -, \<lbrace>\<lambda>rv s. \<not> is_timeout_fault rv\<rbrace>"
  apply (simp add: lookup_reply_def, wpsimp)
  done

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active and ct_not_in_release_q
    and ct_not_queued and scheduler_act_sane and current_time_bounded 1
    and (\<lambda>s. released_if_bound_sc_tcb_at (cur_thread s) s)\<rbrace>
   handle_recv is_blocking can_reply
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (intro hoare_seq_ext_skip hoare_seq_ext_skipE
               catch_wp[OF handle_fault_valid_sched]
               weaker_hoare_ifE[where P=P and P'=P for P, simplified pred_conj_def, simplified];
         wpsimp wp: receive_ipc_valid_sched receive_signal_valid_sched;
         clarsimp simp: ct_in_state_def)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps)

crunch valid_sched[wp]: reply_from_kernel "valid_sched::det_state \<Rightarrow> _"

end

context DetSchedSchedule_AI begin
crunch valid_sched[wp]: invoke_irq_control "valid_sched::'state_ext state \<Rightarrow> _"
  (wp: maybeM_inv)

lemma invoke_irq_handler_valid_sched[wp]:
  "\<lbrace> valid_sched and invs and simple_sched_action\<rbrace>
   invoke_irq_handler i
   \<lbrace> \<lambda>_. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  by (cases i; wpsimp wp: cap_delete_one_valid_sched)

end

declare valid_idle_etcb_lift[wp del]

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
  apply (clarsimp simp: valid_idle_etcb_def etcb_at'_def vs_all_heap_simps valid_idle_def
                        pred_tcb_at_def obj_at_def)
  done


lemma thread_set_domain_not_switch_switch_in_cur_domain:
  "\<lbrace>switch_in_cur_domain and (\<lambda>s. scheduler_action s \<noteq> switch_thread tptr)\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at'_def vs_all_heap_simps
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

lemma thread_set_domain_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain and not_cur_thread t\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_2_def etcb_at'_def vs_all_heap_simps
                        not_cur_thread_def)
  done

lemma thread_set_domain_valid_ready_qs_not_q:
  "\<lbrace>valid_ready_qs and not_queued t\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps  not_queued_def
                  dest!: get_tcb_SomeD split: option.splits)
  apply (intro conjI; clarsimp)
  apply (drule_tac x=d and y =p in spec2, clarsimp, drule_tac x=ta in bspec, simp)
  apply clarsimp
  apply (rule_tac x=ref' in exI, clarsimp)
  done

lemma thread_set_domain_not_idle_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not tptr and not_queued tptr
     and (\<lambda>s. tptr \<noteq> cur_thread s) and (\<lambda>s. tptr \<noteq> idle_thread s) and valid_idle\<rbrace>
     thread_set_domain tptr d \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_valid_ready_qs_not_q thread_set_domain_ct_in_cur_domain
                    thread_set_domain_not_switch_switch_in_cur_domain valid_blocked_lift
                    thread_set_domain_not_idle_valid_idle_etcb)
  apply (clarsimp simp: scheduler_act_not_def not_cur_thread_def)
  done

lemma thread_set_domain_schedulable_bool_not[wp]:
  "\<lbrace>\<lambda>s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        thread_set_domain t d
           \<lbrace>\<lambda>rv s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: thread_set_domain_def thread_set_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_rev is_schedulable_bool_def is_sc_active_def in_release_queue_def
        dest!: get_tcb_SomeD split: option.splits if_split_asm)

lemma thread_set_domain_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        thread_set_domain t d
           \<lbrace>\<lambda>rv s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: thread_set_domain_def thread_set_def wp: set_object_wp)
  by (fastforce simp: get_tcb_rev is_schedulable_bool_def is_sc_active_def in_release_queue_def
        dest!: get_tcb_SomeD split: option.splits)

lemma tcb_sched_action_schedulable_bool_not[wp]:
  "\<lbrace>\<lambda>s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        tcb_sched_action f t
           \<lbrace>\<lambda>rv s. \<not> is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_set_def thread_get_def
                  wp: set_object_wp set_tcb_queue_wp)
  by (clarsimp simp: is_schedulable_bool_def get_tcb_rev obj_at_def dest!: get_tcb_SomeD split: option.splits)

lemma tcb_sched_action_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>
        tcb_sched_action f t
   \<lbrace>\<lambda>rv s. is_schedulable_bool t (in_release_queue t s) s\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_set_def thread_get_def
                  wp: set_object_wp set_tcb_queue_wp)
  by (fastforce simp: is_schedulable_bool_def get_tcb_rev obj_at_def dest!: get_tcb_SomeD split: option.splits)

(* move *)
lemma valid_sched_action_switch_thread_is_schedulable:
  "\<lbrakk>valid_sched_action s; scheduler_action s = switch_thread thread\<rbrakk> \<Longrightarrow>
     is_schedulable_opt thread (in_release_queue thread s) s = Some True"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
       is_schedulable_opt_def pred_tcb_at_def  obj_at_def get_tcb_rev
       in_release_queue_def released_sc_tcb_at_def vs_all_heap_simps is_sc_active_kh_simp)

lemma thread_set_domain_is_schedulable_opt[wp]:
  "\<lbrace>\<lambda>s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>
   thread_set_domain t d
   \<lbrace>\<lambda>rv s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>"
  unfolding thread_set_domain_def
  apply (wpsimp wp: thread_set_wp)
  by (auto simp: is_schedulable_opt_def get_tcb_def is_sc_active_def in_release_queue_def
          split: option.splits kernel_object.splits cong: conj_cong)

lemma tcb_sched_dequeue_is_schedulable_opt[wp]:
  "\<lbrace>\<lambda>s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>
   tcb_sched_action tcb_sched_dequeue t
   \<lbrace>\<lambda>rv s. Q (is_schedulable_opt t (in_release_queue t s) s)\<rbrace>"
  unfolding tcb_sched_action_def
  apply (wpsimp wp: thread_set_wp set_tcb_queue_wp)
  done

lemma valid_blocked_valid_ready_qs_ready_and_sufficient:
  "\<lbrakk>t \<noteq> cur_thread s; valid_ready_qs s; valid_blocked s;
          scheduler_act_not t s;
          st_tcb_at runnable t s; active_sc_tcb_at t s; not_in_release_q t s\<rbrakk>
         \<Longrightarrow> budget_ready t s \<and> budget_sufficient t s"
  apply (clarsimp simp: valid_blocked_defs scheduler_act_not_def valid_ready_qs_def
                        vs_all_heap_simps pred_tcb_at_def obj_at_def in_ready_q_def)
  apply (drule_tac x=t in spec)
  apply (case_tac "tcb_state tcb"; simp)
   apply fastforce
  by fastforce

context DetSchedSchedule_AI begin

lemma invoke_domain_valid_sched:
  notes tcb_sched_enqueue_valid_sched[wp del]
  shows
  "\<lbrace>valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and ct_not_queued
                and scheduler_act_not t and valid_idle
                and (\<lambda>s. budget_ready (cur_thread s) s)\<rbrace>
   invoke_domain t d
   \<lbrace>\<lambda>_. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (simp add: invoke_domain_def)
  including no_pre
  apply wp
  apply (simp add: set_domain_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac "t=cur"; simp)
    (* first case *)
   apply (wpsimp wp_del: reschedule_valid_sched_const wp: reschedule_required_valid_sched')
    apply (wpsimp wp: thread_set_domain_valid_ready_qs_not_q
                      thread_set_domain_not_idle_valid_idle_etcb)
   apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                     tcb_sched_dequeue_valid_blocked_except_set_remove hoare_vcg_conj_lift)
   apply (clarsimp simp: valid_sched_def valid_blocked_defs)
    (* second case *)
  apply (wpsimp wp: tcb_sched_enqueue_valid_sched)
     apply (wpsimp wp: is_schedulable_wp')+
   apply (clarsimp split: if_split)
   apply (wpsimp wp: hoare_vcg_imp_lift')
    apply (simp add: valid_sched_def)
    apply (wpsimp wp: thread_set_domain_valid_ready_qs_not_q
                      thread_set_domain_act_not_valid_sched_action
                      thread_set_domain_ct_in_cur_domain
                      thread_set_domain_not_idle_valid_idle_etcb)
   apply (wpsimp wp: hoare_vcg_imp_lift' thread_set_domain_not_idle_valid_sched)
  apply (clarsimp simp: tcb_at_kh_simps[symmetric] valid_sched_def)
  apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs tcb_dequeue_not_queued
                    tcb_sched_action_valid_sched_misc
                    tcb_sched_dequeue_valid_blocked_except_set_const
                    hoare_vcg_conj_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: valid_blocked_thread_def)
  apply (intro conjI)
   using valid_blocked_valid_ready_qs_ready_and_sufficient apply blast
  apply (clarsimp simp: runnable_eq_active tcb_at_kh_simps)
  done

lemma sched_context_bind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     sched_context_bind_ntfn x21 x41
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
 unfolding sched_context_bind_ntfn_def
 by wpsimp

lemma refill_unblock_check_budget_ready_ct[wp]:
  "\<lbrace>\<lambda>s. budget_ready (cur_thread s) s \<and> valid_machine_time s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_ready (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf_pre_conj[where f=cur_thread]) wpsimp+

lemma refill_unblock_check_budget_sufficient_ct[wp]:
  "\<lbrace>\<lambda>s. budget_sufficient (cur_thread s) s \<and> active_sc_tcb_at (cur_thread s) s \<and> active_sc_valid_refills s\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>xc s. budget_sufficient (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<forall>t. t = cur_thread s \<longrightarrow> budget_sufficient t s" in hoare_strengthen_post[rotated],
         clarsimp)
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

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

crunch sc_tcb_sc_at_inv[wp]: do_machine_op "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                \<and> budget_ready t s \<and> budget_sufficient t s) scp s"
  (simp: crunch_simps split_def sc_tcb_sc_at_def wp: crunch_wps hoare_drop_imps)

crunch sc_tcb_sc_at_inv[wp]: store_word_offs "\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                \<and> budget_ready t s \<and> budget_sufficient t s) scp s"
  (simp: crunch_simps split_def wp: crunch_wps hoare_drop_imps ignore: do_machine_op)

lemma sched_context_yield_to_valid_sched_helper:
  "\<lbrace>sc_yf_sc_at ((=) sc_yf_opt) sc_ptr and
       (valid_sched and simple_sched_action and
        (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s) and
        ct_active and ct_released and invs and ct_not_in_release_q
        and current_time_bounded 1)\<rbrace>
     when (sc_yf_opt \<noteq> None) $
       do complete_yield_to (the sc_yf_opt);
          sc_yf_opt <- get_sc_obj_ref sc_yield_from sc_ptr;
          assert (sc_yf_opt = None)
       od
   \<lbrace>\<lambda>_. valid_sched and simple_sched_action and
     (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s) and
     ct_active and ct_released and invs and current_time_bounded 1\<rbrace>"
  by (wpsimp wp: get_sc_obj_ref_wp complete_yield_to_invs
                 hoare_vcg_all_lift hoare_drop_imp is_schedulable_wp
      | wps)+

lemma sched_context_resume_ready_and_sufficient:
  "\<lbrace> (\<lambda>s. sym_refs (state_refs_of s)) and bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>rv s. is_schedulable_bool tcbptr (in_release_q tcbptr s) s
                \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s\<rbrace>"
  unfolding sched_context_resume_def maybeM_def assert_opt_def
            get_sc_refill_ready_def get_sc_refill_sufficient_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp], rename_tac sc)
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (clarsimp simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp simp: get_refills_def)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (case_tac "runnable ts \<and> sc_active sc \<and>
                     (refill_ready cur_timea (refill_hd xa) \<longrightarrow>
                          \<not> refill_sufficient 0 (refill_hd sca))"; clarsimp)
      (* \<not> (ready \<and> sufficient) *)
    apply (rule_tac Q="\<lambda>_. in_release_q tcbptr" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: is_schedulable_bool_def split: option.splits)
    apply (wpsimp wp: postpone_in_release_q thread_get_wp)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def pred_tcb_at_def)
    apply (drule (1) sym_ref_tcb_sc[where tp=tcbptr])
     apply (drule sym[where s="Some sc_ptr"], simp)
    apply clarsimp
   apply wpsimp
   apply (subgoal_tac "runnable xd \<and> active_sc_tcb_at tcbptr xh")
    apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps)
   apply (clarsimp simp: is_schedulable_bool_def vs_all_heap_simps obj_at_kh_kheap_simps
                  split: option.splits)
  apply wpsimp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule (1) sym_ref_tcb_sc[where tp=tcbptr])
   apply (drule sym[where s="Some sc_ptr"], simp)
  apply clarsimp
  done

lemma sched_context_resume_schedulable:
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr and
       (\<lambda>s. is_schedulable_bool tcbptr (in_release_q tcbptr s) s) and
        budget_ready tcbptr and budget_sufficient tcbptr\<rbrace>
    sched_context_resume sc_ptr
   \<lbrace>\<lambda>rv s. is_schedulable_bool tcbptr (in_release_q tcbptr s) s\<rbrace>"
  unfolding sched_context_resume_def maybeM_def assert_opt_def
            get_sc_refill_ready_def get_sc_refill_sufficient_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (clarsimp simp: bind_assoc)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp simp: get_refills_def)
   apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
   apply (case_tac "runnable ts \<and>
                      sc_active sc \<and>
                      (refill_ready cur_timea (refill_hd xa) \<longrightarrow>
                          \<not> refill_sufficient 0 (refill_hd sca))"; clarsimp)
      (* \<not> (ready \<and> sufficient) *)
    apply (wp hoare_pre_cont)
    apply (clarsimp simp: obj_at_def vs_all_heap_simps pred_tcb_at_def)
   by wpsimp+

crunches sched_context_resume
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P p s)"
    (wp: crunch_wps simp: crunch_simps)

lemma schedulable_not_in_release_q:
  "is_schedulable_bool tp (in_release_q tp s) s \<Longrightarrow> not_in_release_q tp s"
  by (clarsimp simp: is_schedulable_bool_def not_in_release_q_def
               split: option.splits)

lemma refill_unblock_check_ct_released:
  "\<lbrace>ct_released and valid_machine_time and active_sc_valid_refills\<rbrace>
   refill_unblock_check sc_ptr
   \<lbrace>\<lambda>_. ct_released\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf_pre_conj'[where f=cur_thread])
    apply (wpsimp, assumption)
   apply wpsimp
  apply clarsimp
  done

(* end *)

crunches sched_context_resume
  for pred_tcb_at_ct[wp]: "\<lambda>s. pred_tcb_at P proj (cur_thread s) s"
    (wp: crunch_wps simp: crunch_simps)

lemma schedulable_sc_not_in_release_q:
  "\<lbrakk>\<forall>tp. bound_sc_tcb_at ((=) (Some scp)) tp s \<and> is_schedulable_bool tp (in_release_q tp s) s\<rbrakk>
       \<Longrightarrow> sc_not_in_release_q scp s"
  by (fastforce simp: is_schedulable_bool_def split: option.splits)

crunches tcb_sched_action
  for sc_ko_at[wp]: "\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)"

(* use valid blocked to argue that the thread must be in the ready qs *)
lemma sched_context_yield_to_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
    and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s)
    and ct_active and ct_released and invs and ct_not_in_release_q
    and current_time_bounded 1\<rbrace>
   sched_context_yield_to sc_ptr args
   \<lbrace>\<lambda>y. valid_sched\<rbrace>"
  supply if_split[split del]
  unfolding sched_context_yield_to_def assert_opt_def
  apply (rule hoare_seq_ext[OF _ gscyf_sp])
  apply (rule hoare_seq_ext[OF _ sched_context_yield_to_valid_sched_helper], simp)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac sc_tcb_opt; clarsimp)
  apply (rename_tac tcb_ptr)

  apply (rule hoare_seq_ext_skip)
   apply ((wpsimp wp: sched_context_resume_ready_and_sufficient sched_context_resume_schedulable
                      sched_context_resume_valid_sched hoare_vcg_conj_lift
                      sched_context_resume_ct_in_state[simplified ct_in_state_def]
           | wps)+)[1]
   apply (frule invs_sym_refs)
   apply (simp add: heap_refs_retract_eq)

  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (clarsimp simp: is_schedulable_bool_def2)
  apply (case_tac schedulable; clarsimp?, (solves \<open>wpsimp\<close>)?)

  apply (rule hoare_seq_ext_skip)
   apply ((wpsimp wp: hoare_vcg_conj_lift refill_unblock_check_valid_sched is_schedulable_wp
                      refill_unblock_check_sc_tcb_sc_at
                      refill_unblock_check_active_sc_valid_refills refill_unblock_check_ct_released
                      refill_unblock_check_ct_in_state[simplified ct_in_state_def]
           | wps)+)[1]
   apply (intro conjI; (solves \<open>clarsimp simp: valid_sched_def\<close>)?)
   apply (rule allI, rename_tac t)
   apply (clarsimp simp: vs_all_heap_simps sc_at_pred_n_def obj_at_def)
   apply (frule invs_sym_refs)
   apply (frule_tac tp=t in sym_ref_tcb_sc, blast, blast, simp)

  apply (intro hoare_seq_ext[OF _ get_sched_context_sp]
               hoare_seq_ext[OF _ gets_sp]
               hoare_seq_ext[OF _ assert_sp]
               hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_if)
   apply (clarsimp simp: is_schedulable_bool_def2)
   apply (rule_tac B="\<lambda>_ s. valid_sched_except_blocked s
                            \<and> valid_blocked_except tcb_ptr s
                            \<and> invs s
                            \<and> st_tcb_at runnable tcb_ptr s
                            \<and> active_sc_tcb_at tcb_ptr s
                            \<and> not_in_release_q tcb_ptr s
                            \<and> sc_tcb_sc_at ((=) (Some tcb_ptr)) sc_ptr s
                            \<and> sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s
                            \<and> (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)
                            \<and> cur_time s = curtime
                            \<and> sc_refill_ready curtime sc
                            \<and> sc_refill_sufficient 0 sc"
                 in hoare_seq_ext[rotated])
    apply ((wpsimp wp: tcb_sched_dequeue_valid_blocked_except_set'
                       tcb_sched_dequeue_valid_sched_except_blocked tcb_sched_action_sc_tcb_sc_at
            | wps)+)[1]
    apply (clarsimp simp: valid_sched_def)
   apply (rule_tac B="\<lambda>_. valid_sched" in hoare_seq_ext[rotated]; (solves \<open>wpsimp\<close>)?)
    apply (wpsimp wp: tcb_sched_enqueue_valid_sched)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)
    apply (frule invs_sym_refs)
    apply (frule_tac scp=sc_ptr in sym_ref_sc_tcb, blast, blast, force)

  apply (wpsimp wp: set_scheduler_action_swt_valid_sched tcb_sched_dequeue_valid_blocked_except_set
                    tcb_sched_dequeue_valid_sched_except_blocked)
  apply (clarsimp simp: valid_sched_def)
  apply (intro conjI)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)
   apply (frule invs_sym_refs)
   apply (frule_tac scp=sc_ptr in sym_ref_sc_tcb, blast, blast, force)
  apply (fastforce simp: in_cur_domain_def obj_at_def etcb_at_def vs_all_heap_simps)
  done

lemma invoke_sched_context_valid_sched:
  "\<lbrace>invs and valid_sched and valid_sched_context_inv iv and invs and simple_sched_action
    and ct_not_in_release_q and ct_active and ct_released and current_time_bounded 1\<rbrace>
   invoke_sched_context iv
   \<lbrace>\<lambda>_. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (cases iv; simp)
      apply (wpsimp simp: invoke_sched_context_def
                  wp: sched_context_bind_tcb_valid_sched
                      sched_context_unbind_tcb_valid_sched sched_context_yield_to_valid_sched)+
     apply (rename_tac ref s cap)
     apply (prop_tac "sched_context_donate_ipc_queues_precond cap ref s")
      apply (simp add: obj_at_kh_kheap_simps pred_map_ipc_queued_thread_state_iff;
             fastforce simp: pred_map_def pred_map_weakenE)
     apply (clarsimp simp: not_cur_thread_def vs_all_heap_simps obj_at_kh_kheap_simps)
    apply (wpsimp simp: invoke_sched_context_def
                wp: sched_context_bind_tcb_valid_sched
                    sched_context_unbind_tcb_valid_sched sched_context_yield_to_valid_sched)+
  done

(* FIXME RT: move *)
lemma update_sched_context_known_sc:
  assumes "kheap s sc_ptr = Some (SchedContext sc n)"
  shows "update_sched_context sc_ptr (\<lambda>_. f sc) s = update_sched_context sc_ptr f s"
  using assms
  by (auto simp: obj_at_def update_sched_context_def get_object_def set_object_def
                 gets_def get_def assert_def return_def put_def fail_def bind_def)

(* FIXME RT: move *)
\<comment> \<open>For expanding a batch field update into individual field updates, you typically want to expand
    all but the last update. To do this safely in simplification, it is necessary to fix both
    f and g. For that purpose, the "ext2" version below is probably the lemma you want.\<close>
lemma update_sched_context_decompose:
  "update_sched_context scp (\<lambda>sc. f (g sc))
   = do update_sched_context scp g; update_sched_context scp f od"
  apply (rule ext, rename_tac s)
  by (clarsimp simp: update_sched_context_def get_object_def set_object_def a_type_simps
                     gets_def get_def put_def return_def fail_def assert_def bind_def
              split: kernel_object.splits)

(* FIXME RT: move *)
lemmas update_sched_context_decompose_ext = update_sched_context_decompose[where f="f x" and g="g y" for f g x y]
lemmas update_sched_context_decompose2 = update_sched_context_decompose[where g="\<lambda>sc. g (h sc)" for g h]
lemmas update_sched_context_decompose_ext2 = update_sched_context_decompose2[where f="f x" and g="g y" for f g x y]

(* FIXME RT: make this the definition, since individual field updates work better with heap projection machinery. *)
lemma refill_new_def2:
  "refill_new sc_ptr max_refills budget period \<equiv> do
       assert (MIN_BUDGET < budget);
       cur_time <- gets cur_time;
       set_sc_obj_ref sc_period_update sc_ptr period;
       set_sc_obj_ref sc_refills_update sc_ptr [\<lparr>r_time = cur_time, r_amount = budget\<rparr>];
       set_sc_obj_ref sc_refill_max_update sc_ptr max_refills;
       set_sc_obj_ref sc_budget_update sc_ptr budget
     od"
  unfolding refill_new_def
  unfolding update_sched_context_decompose_ext2[where f=sc_budget_update and g=sc_refill_max_update]
            update_sched_context_decompose_ext2[where f=sc_refill_max_update and g=sc_refills_update]
            update_sched_context_decompose_ext2[where f=sc_refills_update and g=sc_period_update]
  by (simp add: bind_assoc)

(* FIXME RT: make this the definition, since individual field updates work better with heap projection machinery. *)
lemma refill_update_def2:
  "refill_update sc_ptr new_period new_budget new_max_refills \<equiv> do
       sc <- get_sched_context sc_ptr;
       refill_hd <- return $ refill_hd sc;
       cur_time <- gets cur_time;
       ready <- get_sc_refill_ready sc_ptr;
       new_time <- return $ if ready then cur_time else r_time refill_hd;
       if new_budget \<le> r_amount refill_hd then do set_sc_obj_ref sc_period_update sc_ptr new_period;
                                                   set_sc_obj_ref sc_refill_max_update sc_ptr new_max_refills;
                                                   set_sc_obj_ref sc_refills_update sc_ptr [\<lparr>r_time = new_time, r_amount = new_budget\<rparr>];
                                                   set_sc_obj_ref sc_budget_update sc_ptr new_budget
                                                od
       else do unused <- return $ new_budget - r_amount refill_hd;
               new <- return $ \<lparr>r_time = r_time refill_hd + new_period - unused, r_amount = unused\<rparr>;
               new_refills <- return $ schedule_used False [refill_hd] new;
               set_sc_obj_ref sc_period_update sc_ptr new_period;
               set_sc_obj_ref sc_refill_max_update sc_ptr new_max_refills;
               set_sc_obj_ref sc_refills_update sc_ptr new_refills;
               set_sc_obj_ref sc_budget_update sc_ptr new_budget
            od
    od"
  unfolding refill_update_def atomize_eq
  unfolding update_sched_context_decompose_ext2[where f=sc_budget_update and g=sc_refills_update]
            update_sched_context_decompose_ext2[where f=sc_refills_update and g=sc_refill_max_update]
            update_sched_context_decompose_ext2[where f=sc_refill_max_update and g=sc_period_update]
  apply (simp add: bind_assoc)
  supply if_split[split del]
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_bind_tail[OF _ get_sched_context_sp], simp)
  apply (rule monadic_rewrite_bind_tail[OF _ gets_inv])
  apply (rule monadic_rewrite_bind_tail[OF _ get_sc_refill_ready_inv])
  apply (rule monadic_rewrite_if[where Q=R and R=R for R, simplified]
         ; rule monadic_rewrite_bind_head[OF monadic_rewrite_refl3])
  by (auto simp: obj_at_def update_sched_context_known_sc)

lemma refill_new_valid_sched_misc[wp]:
  "refill_new sc_ptr max_refills budget period
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)\<rbrace>"
  unfolding refill_new_def2 by wpsimp

lemma refill_update_valid_sched_misc[wp]:
  "refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (sc_tcbs_of s)
          (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s) (last_machine_time_of s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_replies_of s)\<rbrace>"
  unfolding refill_update_def2 by wpsimp

crunches set_refills, refill_update, refill_new
  for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at Q t s)"

lemma sc_ready_times_cong:
  assumes "tcbs = tcbs'"
  assumes "sc_ready_times_2 scs = sc_ready_times_2 scs'"
  shows "sc_ready_times_2 (tcb_sc_refill_cfgs_2 tcbs scs) = sc_ready_times_2 (tcb_sc_refill_cfgs_2 tcbs' scs')"
  by (clarsimp simp: sc_ready_times_2_def tcb_sc_refill_cfgs_2_def map_project_opt_map
                     assms[unfolded sc_ready_times_2_def])

lemma refill_update_sc_tcb_sc_at[wp]:
  "refill_update sc_ptr mrefills budget period \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma refill_new_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (fastforce simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_resume_cond_released_sc_tcb_at':
  "\<lbrace>bound_sc_tcb_at ((=) (Some sc_ptr)) tcbptr
    and sc_tcb_sc_at ((=) (Some tcbptr)) sc_ptr
    and st_tcb_at runnable tcbptr
    and active_sc_tcb_at tcbptr\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>rv s :: 'state_ext state. not_in_release_q tcbptr s \<longrightarrow> released_sc_tcb_at tcbptr s \<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: hoare_vcg_imp_lift' thread_get_wp is_schedulable_wp postpone_in_release_q)+
  apply (safe; clarsimp simp: obj_at_def pred_tcb_at_def sc_at_pred_n_def
                              is_schedulable_bool_def2 is_tcb vs_all_heap_simps)
  done

lemma update_sched_context_not_active_sc_tcb_at:
  "\<lbrace>\<lambda>s. \<not> active_sc_tcb_at t s
        \<and> (\<forall>sc. pred_map_eq (Some sc_ptr) (tcb_scps_of s) t
                \<longrightarrow> \<not> sc_active (f sc))\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>x s. \<not> active_sc_tcb_at t s\<rbrace>"
   apply (wpsimp wp: update_sched_context_wp)
   apply (clarsimp simp: vs_all_heap_simps split: if_splits)
   done

lemma set_refills_ep_at_pred[wp]:
  "set_refills sc_ptr refills \<lbrace>\<lambda>s. Q (ep_at_pred P p s)\<rbrace>"
  unfolding set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_def simple_obj_at_def split: if_splits)
  done

lemma refill_update_valid_blocked:
  "\<lbrace>valid_blocked and K (0 < mrefills) and is_sc_active sc_ptr\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  unfolding refill_update_def valid_blocked_defs
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' update_sched_context_not_active_sc_tcb_at)
  by (auto simp: vs_all_heap_simps is_sc_active_kh_simp)

lemma refill_new_active_sc_tcb_at:
  "\<lbrace>\<lambda>s. if (pred_map_eq (Some sc_ptr) (tcb_scps_of s) t) then 0 < mrefills else active_sc_tcb_at t s\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps active_sc_def)
  apply (prop_tac "t \<noteq> sc_ptr"; clarsimp)
  by (fastforce split: if_splits)

lemma refill_new_valid_blocked_no_sc_tcb:
  "\<lbrace>valid_blocked and K (0 < mrefills)
    and (\<lambda>s. \<exists>sc n. kheap s sc_ptr = Some (SchedContext sc n) \<and> sc_tcb sc = None)
    and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  unfolding refill_new_def valid_blocked_defs
  apply (wpsimp wp: hoare_vcg_all_lift)
  apply (rule hoare_vcg_imp_lift')
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
                    update_sched_context_not_active_sc_tcb_at)+
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps pred_map_eq_def)
  by (frule sym_ref_tcb_sc; fastforce?)


lemma refill_new_not_active_sc:
  "\<lbrace>\<lambda>s. if (scp = sc_ptr) then mrefills = 0 else \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv s.  \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps active_sc_def split: if_splits)

lemma refill_new_bounded_release_time[wp]:
  "\<lbrace>\<lambda>s. if p = scp
        then (\<exists>sc n. kheap s p = Some (SchedContext sc n)
             \<and> unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time)
        else bounded_release_time scp s\<rbrace>
   refill_new p max_refills budget period
   \<lbrace>\<lambda>s. bounded_release_time scp\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: pred_map_simps vs_all_heap_simps cfg_bounded_release_time_def)

lemma refill_new_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and (\<lambda>s. unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time)
    and K (MIN_REFILLS \<le> max_refills \<and> budget \<le> period \<and> MIN_SC_BUDGET \<le> budget \<and> period \<le> MAX_SC_PERIOD)
    and (\<lambda>s. \<exists>sc n. kheap s p = Some (SchedContext sc n)) \<rbrace>
   refill_new p max_refills budget period
   \<lbrace>\<lambda>rv. active_sc_valid_refills\<rbrace>"
  unfolding active_sc_valid_refills_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_new_not_active_sc)
  apply (subgoal_tac "unat (cur_time s) + unat period \<le> unat max_time")
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps pred_map_eq_def split: if_splits)
  apply (erule add_left_mono_trans, overflow_hammer)
  done

lemma refill_update_not_active_sc:
  "\<lbrace>\<lambda>s. if (scp = sc_ptr) then mrefills = 0 else \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv s.  \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  by (clarsimp simp: vs_all_heap_simps active_sc_def split: if_splits)

lemma refill_update_bounded_release_time:
  "\<lbrace>bounded_release_time scp
    and K (MIN_SC_BUDGET \<le> budget)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. bounded_release_time scp\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  by (auto simp: pred_map_simps vs_all_heap_simps cfg_bounded_release_time_def obj_at_def
                 MIN_SC_BUDGET_def)

lemma refill_update_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and current_time_bounded 2
    and K (MIN_REFILLS \<le> max_refills \<and> budget \<le> period \<and> MIN_SC_BUDGET \<le> budget \<and> period \<le> MAX_SC_PERIOD)
    and is_active_sc p\<rbrace>
   refill_update p period budget max_refills
   \<lbrace>\<lambda>rv. active_sc_valid_refills\<rbrace>"
  unfolding active_sc_valid_refills_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_update_not_active_sc
                    refill_update_bounded_release_time)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps pred_map_eq_def current_time_bounded_def)
  apply (drule_tac x=p in spec; clarsimp)
  apply (intro conjI impI)
    apply (rule order_trans, rule add_left_mono, rule mult_le_mono2, erule iffD1[OF unat_le_mono])
    apply (clarsimp)
   apply (clarsimp simp: bounded_release_time_def mult_2 add.assoc[symmetric])
   apply (rule order_trans, erule add_right_mono)
   apply (erule order_trans[rotated])
   apply (rule add_left_mono, erule iffD1[OF unat_le_mono])
  apply (rule order_trans, rule add_left_mono, rule mult_le_mono2, erule iffD1[OF unat_le_mono])
  apply (clarsimp)
  done

lemma update_sched_context_budget_ready:
  "\<lbrace>\<lambda>s. if bound_sc_tcb_at ((=) (Some scp)) t s
        then sc_refill_ready (cur_time s) sc
        else budget_ready t s\<rbrace>
   update_sched_context scp (\<lambda>_. sc)
   \<lbrace>\<lambda>rv. budget_ready t\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  by (fastforce simp: obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)

lemma update_sched_context_budget_sufficient:
  "\<lbrace>\<lambda>s. if bound_sc_tcb_at ((=) (Some scp)) t s
        then sc_refill_sufficient 0 sc
        else budget_sufficient t s\<rbrace>
   update_sched_context scp (\<lambda>_. sc)
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)
   apply fastforce
  apply (prop_tac "t \<noteq> scp"; fastforce)
  done

lemma update_sched_context_active_sc_tcb_at:
  "\<lbrace>\<lambda>s. if bound_sc_tcb_at ((=) (Some scp)) t s
        then sc_active sc
        else active_sc_tcb_at t s\<rbrace>
   update_sched_context scp (\<lambda>_. sc)
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)
   apply fastforce
  apply (prop_tac "t \<noteq> scp"; fastforce)
  done

lemma refill_update_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t and valid_machine_time and K (active_sc mrefills)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  supply if_split [split del]
  unfolding refill_update_def
  by (wpsimp wp: update_sched_context_active_sc_tcb_at)

lemma refill_update_active_sc_tcb_at':
  "\<lbrace>\<lambda>s. if bound_sc_tcb_at ((=) (Some sc_ptr)) t s then active_sc mrefills
       else active_sc_tcb_at t s\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. active_sc_tcb_at t\<rbrace>"
  supply if_split [split del]
  unfolding refill_update_def
  by (wpsimp wp: update_sched_context_active_sc_tcb_at)

lemma refill_update_budget_sufficient:
  "\<lbrace>budget_sufficient t and K (MIN_BUDGET \<le> budget)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>"
  supply if_split [split del]
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_budget_sufficient)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps split: if_splits)
  apply (clarsimp simp: refill_sufficient_defs)
  apply (intro conjI impI; simp)
  apply (rule word_sub_mono3[where x = MIN_BUDGET])
   apply (fastforce)
  apply (simp only: mult_2[symmetric] MIN_SC_BUDGET_def[symmetric])
  apply (rule MIN_BUDGET_le_MIN_SC_BUDGET)
  done

lemma refill_update_budget_ready_indep:
  "\<lbrace>budget_ready t and (Not \<circ> bound_sc_tcb_at (\<lambda>p. p = Some sc_ptr) t)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. budget_ready t\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_budget_ready)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma refill_update_budget_sufficient_indep:
  "\<lbrace>budget_sufficient t and (Not \<circ> bound_sc_tcb_at (\<lambda>p. p = Some sc_ptr) t)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_budget_sufficient)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma refill_update_active_sc_tcb_at_indep:
  "\<lbrace>(\<lambda>s. P (active_sc_tcb_at t s)) and (Not \<circ> bound_sc_tcb_at (\<lambda>p. p = Some sc_ptr) t)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding refill_update_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (intro impI conjI allI; erule back_subst[where P=P])
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps)

lemma refill_update_released_sc_tcb_at_indep:
  "\<lbrace>released_sc_tcb_at t and (Not \<circ> bound_sc_tcb_at (\<lambda>p. p = Some sc_ptr) t)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. released_sc_tcb_at t\<rbrace>"
  by (wpsimp wp: refill_update_budget_ready_indep refill_update_budget_sufficient_indep
                 refill_update_active_sc_tcb_at_indep
           simp: released_sc_tcb_at_def)

lemma refill_update_valid_ready_qs:
  "\<lbrace>valid_ready_qs and (\<lambda>s. \<forall>t. (bound_sc_tcb_at (\<lambda>p. p = Some sc_ptr) t) s \<longrightarrow> not_queued t s)\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  unfolding valid_ready_qs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_update_released_sc_tcb_at_indep
           simp: Ball_def not_queued_def)

lemma refill_update_sorted_release_q:
  "\<lbrace>\<lambda>s. sorted_release_q s \<and> sc_not_in_release_q sc_ptr s\<rbrace>
   refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. sorted_release_q\<rbrace>"
  supply if_split[split del]
  apply (rule hoare_lift_Pf2[where f=release_queue, rotated], wpsimp)
  apply (rule sorted_release_q_2_valid_lift)
  apply (simp add: refill_update_def)
  apply (intro hoare_seq_ext_skip hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule update_sched_context_tcb_ready_times_idem; simp add: in_queue_2_def)+
  done

lemma refill_update_valid_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
    refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding valid_release_q_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_update_sorted_release_q
                    refill_update_active_sc_tcb_at_indep
              simp: Ball_def)
  by (clarsimp simp: tcb_at_kh_simps pred_map_simps not_in_release_q_def)

lemma refill_update_released_ipc_queues:
  "\<lbrace>released_ipc_queues and sc_with_tcb_prop sc_ptr not_ipc_queued_thread\<rbrace>
    refill_update sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  unfolding released_ipc_queues_defs
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift
                    refill_update_released_sc_tcb_at_indep refill_update_active_sc_tcb_at_indep
              simp: Ball_def pred_tcb_at_eq_commute[symmetric])
  by (fastforce simp: pred_map_ipc_queued_thread_state_iff tcb_at_kh_simps pred_map_eq_def)

lemma refill_update_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   refill_update sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def weak_valid_sched_action_def
  apply (wpsimp wp: hoare_vcg_conj_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
                    refill_update_budget_ready_indep
                    refill_update_active_sc_tcb_at_indep
                    refill_update_budget_sufficient_indep
              simp: released_sc_tcb_at_def)
  by (clarsimp simp: simple_sched_action_def)

lemma refill_update_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>tcb_ptr.  bound_sc_tcb_at (\<lambda>t. t = (Some sc_ptr)) tcb_ptr s \<longrightarrow> tcb_ptr \<in> S)\<rbrace>
   refill_update sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding valid_blocked_defs
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' refill_update_active_sc_tcb_at_indep)

lemma update_sched_context_valid_ready_qs_helper2:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at ((=) (Some sc_ptr)) tcb_ptr s \<longrightarrow>
                   in_ready_q tcb_ptr s \<longrightarrow>
                   (active_sc mrefills) \<and>
                   refill_sufficient 0 refill \<and>
                   refill_ready (cur_time s) refill)\<rbrace>
   update_sched_context sc_ptr (\<lambda>sc. sc \<lparr>sc_period := period, sc_refills := [refill],
                                sc_refill_max := mrefills, sc_budget := budget\<rparr>)
   \<lbrace>\<lambda>r. valid_ready_qs\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_ready_qs_def vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (subgoal_tac "t \<noteq> sc_ptr", clarsimp)
   apply (rule_tac x=ref' in exI, clarsimp)
   apply (fastforce simp: in_ready_q_def)
  by fastforce

lemma refill_new_valid_ready_qs:
  "\<lbrace>valid_ready_qs and K (MIN_BUDGET \<le> budget) and K (active_sc mrefills) and valid_machine_time\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  supply if_split [split del]
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_valid_ready_qs_helper2 set_refills_valid_ready_qs
                    hoare_vcg_all_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift' | wp update_sched_context_wp )+
  apply (clarsimp simp: obj_at_def in_ready_q_def refill_sufficient_defs
                        refill_ready_def)
  by (erule cur_time_no_overflow)

lemma refill_new_budget_ready:
  "\<lbrace>(\<lambda>s. if (pred_map_eq (Some sc_ptr) (tcb_scps_of s) t) then True else budget_ready t s)
    and valid_machine_time\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. budget_ready t\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps refill_ready_def)
  apply (prop_tac "t \<noteq> sc_ptr"; clarsimp)
  by (fastforce split: if_splits dest: cur_time_no_overflow)

lemma refill_new_budget_sufficient:
  "\<lbrace>(\<lambda>s. if (pred_map_eq (Some sc_ptr) (tcb_scps_of s) t) then True else budget_sufficient t s)\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. budget_sufficient t\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps refill_sufficient_defs)
  apply (prop_tac "t \<noteq> sc_ptr"; clarsimp)
  by (fastforce split: if_splits)

lemma refill_new_released_sc_tcb_at:
  "\<lbrace>(\<lambda>s. if (pred_map_eq (Some sc_ptr) (tcb_scps_of s) t) then active_sc mrefills else released_sc_tcb_at t s)
    and valid_machine_time\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. released_sc_tcb_at t\<rbrace>"
  unfolding released_sc_tcb_at_def
  by (wpsimp wp: refill_new_budget_sufficient refill_new_budget_ready
                 refill_new_active_sc_tcb_at
           simp: active_sc_def)

lemma refill_new_schedulable_if_bound_sc_tcb_at:
  "\<lbrace>(\<lambda>s. if pred_map_eq (Some sc_ptr) (tcb_scps_of s) t
         then 0 < mrefills
         else released_if_bound_sc_tcb_at t s)
    and valid_machine_time\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. released_if_bound_sc_tcb_at t\<rbrace>"
  unfolding  pred_conj_def
  by (wpsimp wp: refill_new_budget_sufficient refill_new_budget_ready refill_new_released_sc_tcb_at
                 refill_new_active_sc_tcb_at hoare_vcg_disj_lift hoare_vcg_conj_lift
           simp: active_sc_def)

lemma refill_new_schedulable_ipc_queues:
  "\<lbrace>released_ipc_queues and valid_machine_time and K(0 < mrefills)\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. released_ipc_queues\<rbrace>"
  unfolding released_ipc_queues_defs
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift
                    refill_new_active_sc_tcb_at refill_new_released_sc_tcb_at
              simp: Ball_def pred_tcb_at_eq_commute[symmetric])
  apply (clarsimp simp: active_sc_def)
  done

lemma refill_new_sorted_release_q:
  "\<lbrace>\<lambda>s. sorted_release_q s \<and> sc_not_in_release_q sc_ptr s\<rbrace>
   refill_new sc_ptr period budget mrefills
   \<lbrace>\<lambda>rv. sorted_release_q\<rbrace>"
  supply if_split[split del]
  apply (rule hoare_lift_Pf2[where f=release_queue, rotated], wpsimp)
  apply (rule sorted_release_q_2_valid_lift)
  apply (simp add: refill_new_def)
  apply (intro hoare_seq_ext_skip; (solves \<open>wpsimp\<close>)?)
  apply (rule update_sched_context_tcb_ready_times_idem; simp add: in_queue_2_def sc_refill_cfg_of_def)
  done

lemma refill_new_valid_release_q:
  "\<lbrace>valid_release_q and sc_not_in_release_q sc_ptr\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding valid_release_q_def
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift refill_new_active_sc_tcb_at
                    refill_new_sorted_release_q
              simp: Ball_def)
  by (clarsimp simp: tcb_at_kh_simps pred_map_eq_def not_in_release_q_def)

lemma refill_new_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: is_round_robin_wp update_sched_context_wp set_refills_valid_sched_action)
  by (auto simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def simple_sched_action_def
                 switch_in_cur_domain_def vs_all_heap_simps obj_at_kh_kheap_simps)

lemma refill_new_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and
    (\<lambda>s. \<forall>tcb_ptr. bound_sc_tcb_at (\<lambda>t. t = (Some sc_ptr)) tcb_ptr s \<longrightarrow> tcb_ptr \<in> S)\<rbrace>
   refill_new sc_ptr mrefills budget period
   \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  unfolding refill_new_def set_refills_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: valid_blocked_defs)
  apply (subgoal_tac "pred_map active (tcb_sts_of s) t \<and> active_sc_tcb_at t s")
   apply (fastforce)
  by (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps split: if_splits)

lemma refill_new_is_sc_active:
  "\<lbrace>K (P (active_sc max_refills))\<rbrace>
     refill_new sc_ptr max_refills budget period
   \<lbrace>\<lambda>rv s. P (is_sc_active sc_ptr s)\<rbrace>"
  unfolding refill_new_def
  by (wpsimp wp: update_sched_context_wp)
     (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_sc_active_def)

crunches refill_update, refill_new, set_refills
  for pred_tcb_at[wp]: "pred_tcb_at proj test ptr"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_push_sc_tcb_sc_at:
  "reply_push caller callee reply_ptr False \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
  unfolding reply_push_def
  apply clarsimp
  by (wpsimp wp: hoare_drop_imps)

lemma make_arch_fault_msg_obj_at_sc_tcb_sc_at[wp]:
  "make_arch_fault_msg a b \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P p s)\<rbrace>"
  by (wpsimp simp: sc_tcb_sc_at_def wp: make_arch_fault_msg_obj_at)

crunches possible_switch_to, do_ipc_transfer, postpone
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P p s)"
  (wp: crunch_wps)

lemma send_ipc_sc_tcb_sc_at:
  "send_ipc block call badge can_grant can_grant_reply False thread epptr \<lbrace>sc_tcb_sc_at P sc_ptr\<rbrace>"
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

lemma check_budget_simple_sched_action[wp]:
  "check_budget \<lbrace>simple_sched_action\<rbrace>"
  unfolding check_budget_def charge_budget_def
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_if_lift2)
  done

(* charge_budget *)
lemma tcb_fault_update_sym_refs:
  "thread_set (tcb_fault_update f) tptr
   \<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule_tac P="sym_refs" in back_subst)
  apply (rule ext)
  by (clarsimp simp: state_refs_of_def dest!: get_tcb_SomeD)

crunches end_timeslice
  for valid_sched_misc[wp]:
    "\<lambda>s::'state_ext state. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s)
                             (cur_thread s) (idle_thread s) (etcbs_of s)
                             (last_machine_time_of s) (sc_refill_cfgs_of s)"
  (wp: crunch_wps ignore: thread_set)

lemma end_timeslice_valid_release_q:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> ct_not_in_release_q s \<and> ct_active s \<and> cur_sc_chargeable s
         \<and> heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s)
         \<and> active_sc_tcb_at (cur_thread s) s\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. (valid_release_q)::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  apply (wpsimp wp: handle_timeout_valid_release_q thread_get_wp' postpone_valid_release_q)
  apply (prop_tac "cur_sc_tcb_are_bound s", clarsimp simp: cur_sc_chargeable_def vs_all_heap_simps)
  apply (frule (1) heap_refs_retract_atD)
  by (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise ct_in_state_kh_simp vs_all_heap_simps runnable_eq)

lemma end_timeslice_valid_ready_qs:
  "\<lbrace>valid_ready_qs and valid_sched_action and released_ipc_queues and
    ct_not_queued and ct_active and scheduler_act_sane
    and cur_sc_chargeable
    and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. valid_ready_qs ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  apply (wpsimp wp: handle_timeout_valid_ready_qs thread_get_wp' postpone_valid_ready_qs)
  apply (subgoal_tac "bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s")
   apply (clarsimp dest!: get_tcb_SomeD
                    simp: obj_at_kh_kheap_simps vs_all_heap_simps pred_map_simps
                          ct_in_state_def runnable_eq_active is_timeout_fault_def)
  apply (clarsimp simp: cur_sc_chargeable_def vs_all_heap_simps tcb_at_kh_simps
                 dest!: get_tcb_SomeD)
  done

crunches handle_timeout
  for ready_or_release[wp]: "ready_or_release :: 'state_ext state \<Rightarrow> _"

lemma end_timeslice_ready_or_release[wp]:
  "\<lbrace>ready_or_release and valid_ready_qs and ct_not_in_release_q\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. ready_or_release :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: end_timeslice_def get_tcb_queue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>)+
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>)+
  apply (wpsimp wp: thread_get_wp hoare_drop_imps)
  done

lemma end_timeslice_valid_blocked[wp]:
  "end_timeslice canTimeout \<lbrace>valid_blocked_except_set S ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  by (wpsimp wp: handle_timeout_valid_blocked thread_get_wp'
                 tcb_sched_append_valid_blocked_except_set_const
                 postpone_valid_blocked_except_set)

lemma end_timeslice_released_ipc_queues:
  "\<lbrace>\<lambda>s. released_ipc_queues s \<and> active_sc_tcb_at (cur_thread s) s\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. released_ipc_queues ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  by (wpsimp wp: handle_timeout_released_ipc_queues thread_get_wp' simp: is_timeout_fault_def)

lemma refill_budget_check_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check consumed
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_weak_valid_sched_action_act_not is_round_robin_wp)

lemma refill_budget_check_round_robin_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. sc_scheduler_act_not (cur_sc s) s)\<rbrace>
   refill_budget_check_round_robin consumed
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: set_refills_weak_valid_sched_action_act_not is_round_robin_wp)

lemma refill_budget_check_cur_sc_tcb[wp]:
  "refill_budget_check usage \<lbrace>cur_sc_tcb\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: hoare_drop_imps)

lemma refill_budget_check_active_sc_tcb_at[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: hoare_drop_imp)

lemma refill_budget_check_active_sc_tcb_at':
  assumes "\<And>P. refill_budget_check usage \<lbrace>\<lambda>s. P (t s)\<rbrace>"
  shows "refill_budget_check usage \<lbrace>\<lambda>s. P (active_sc_tcb_at (t s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=t, OF _ assms]) wp

lemmas refill_budget_check_active_sc_tcb_at_ct[wp]
  = refill_budget_check_active_sc_tcb_at'[where t=cur_thread, OF refill_budget_check_valid_sched_misc]

lemma refill_budget_check_round_robin_active_sc_tcb_at[wp]:
  "refill_budget_check_round_robin usage \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: hoare_drop_imp)

lemma refill_budget_check_round_robin_active_sc_tcb_at':
  assumes "\<And>P. refill_budget_check_round_robin usage \<lbrace>\<lambda>s. P (t s)\<rbrace>"
  shows "refill_budget_check_round_robin usage \<lbrace>\<lambda>s. P (active_sc_tcb_at (t s) s)\<rbrace>"
  by (rule hoare_lift_Pf[where f=t, OF _ assms]) wp

lemmas refill_budget_check_round_robin_active_sc_tcb_at_ct[wp]
  = refill_budget_check_round_robin_active_sc_tcb_at'[where t=cur_thread, OF refill_budget_check_round_robin_valid_sched_misc]

lemma invoke_untyped_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)

lemma invoke_untyped_oe[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  "\<lbrace>ct_not_queued\<rbrace>
   invoke_untyped x
   -, \<lbrace>\<lambda>rv. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (rule valid_validE_E, rule hoare_weaken_pre, wps, wpsimp, simp)+

lemma update_time_stamp_released_ipc_queues[wp]:
  "\<lbrace>released_ipc_queues and valid_machine_time\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding released_ipc_queues_defs released_sc_tcb_at_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift update_time_stamp_budget_ready)

crunches cap_delete
  for scheduler_act_sane[wp]: " scheduler_act_sane :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma cap_revoke_scheduler_act_sane:
  "\<lbrace>simple_sched_action\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>rv. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule validE_valid, rule cap_revoke_preservation)
     apply (wpsimp wp: preemption_point_inv  simp: ct_in_state_def)+
  done

lemma cap_delete_ct_not_in_release_qE_E:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   cap_delete x
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_def by wpsimp

lemma set_tcb_obj_ref_ct_in_state_no_change:
  "(\<And>y. P (tcb_state y) \<Longrightarrow> P (tcb_state (f (\<lambda>_. new) y))) \<Longrightarrow>
   set_tcb_obj_ref f ref new \<lbrace>ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma preemption_point_ct_in_state[wp]:
  "preemption_point \<lbrace>ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: preemption_point_inv; clarsimp simp: ct_in_state_def)

(* FIXME: crunch call stack should only display on failure *)
crunches finalise_cap
  for ct_not_blocked[wp]: "ct_not_blocked :: 'state_ext state \<Rightarrow> _"
  (ignore: set_tcb_obj_ref set_object thread_set
       wp: set_thread_state_ct_in_state crunch_wps set_tcb_obj_ref_ct_in_state_no_change thread_set_ct_in_state maybeM_inv)

end

context DetSchedSchedule_AI_det_ext begin

crunches cap_swap_ext, cap_delete
  for ct_not_blocked[wp]: "ct_not_blocked :: det_state \<Rightarrow> _"
  (wp: crunch_wps dxo_wp_weak ignore_del: cap_swap_ext)

end

lemmas rec_del_invs''_CTEDeleteCall = rec_del_invs''
                                      [where call = "(CTEDeleteCall x True)" for x,
                                       simplified,
                                       simplified pred_conj_def,
                                       THEN use_specE']

lemma tcb_release_enqueue_not_in_release_q:
  "\<lbrace>not_in_release_q t' and (\<lambda>s. t \<noteq> t')\<rbrace>
   tcb_release_enqueue t
   \<lbrace>\<lambda>rv. not_in_release_q t'\<rbrace>"
  unfolding tcb_release_enqueue_def
  apply wpsimp
     apply (rule_tac Q="\<lambda>_ _. not_in_release_q_2 (qs) t' \<and> (t \<noteq> t')" in hoare_strengthen_post[rotated])
      apply (fastforce simp: not_in_release_q_def in_queue_2_def intro: in_set_zip1)
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

context DetSchedSchedule_AI begin

lemma cap_delete_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   cap_delete x
   \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_def
  apply (rule_tac Q="\<lambda>_. cur_sc_chargeable and ct_not_blocked and invs "
                   in hoare_strengthen_post)
   apply (wpsimp wp: rec_del_invs''_CTEDeleteCall
                     [where Q="cur_sc_chargeable and ct_not_blocked",
                      simplified])
      apply (wpsimp wp: finalise_cap_cur_sc_chargeable)
     apply (wpsimp simp:)
    apply (wpsimp wp: preemption_point_inv)
   apply (clarsimp simp: ct_in_state_def)+
  done

crunches install_tcb_cap
  for ct_not_blocked[wp]: "ct_not_blocked :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv)

lemma install_tcb_cap_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and ct_not_blocked\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv cap_delete_cur_sc_chargeable)

crunches restart
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: maybeM_inv)

lemma reply_unlink_tcb_ct_in_state_weak:
  "\<lbrace>ct_in_state P and (\<lambda>s. t \<noteq> cur_thread s \<or> P Inactive)\<rbrace>
   reply_unlink_tcb t r
  \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: sts_ctis_neq gts_wp get_simple_ko_wp)

lemma blocked_cancel_ipc_ct_in_state:
  "\<lbrace>ct_in_state P and (\<lambda>s. x \<noteq> cur_thread s \<or> P Inactive)\<rbrace>
   blocked_cancel_ipc a x c
   \<lbrace>\<lambda>rv. ct_in_state P:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding blocked_cancel_ipc_def
  apply (wpsimp wp: set_thread_state_ct_st hoare_vcg_if_lift2 hoare_vcg_imp_lift get_simple_ko_wp
                    reply_unlink_tcb_ct_in_state_weak get_ep_queue_wp get_blocking_object_wp
                    hoare_vcg_disj_lift hoare_vcg_all_lift)
  by auto

lemma reply_remove_tcb_ct_in_state:
  "\<lbrace>ct_in_state P and (\<lambda>s. x \<noteq> cur_thread s \<or> P Inactive)\<rbrace>
   reply_remove_tcb x y
   \<lbrace>\<lambda>rv. ct_in_state P:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding reply_remove_tcb_def
  by (wpsimp wp: set_thread_state_ct_st hoare_vcg_if_lift2 hoare_vcg_imp_lift get_simple_ko_wp
                    reply_unlink_tcb_ct_in_state_weak get_ep_queue_wp get_blocking_object_wp
                    hoare_vcg_disj_lift hoare_vcg_all_lift get_sk_obj_ref_wp gts_wp)

lemma cancel_signal_ct_in_state:
  "\<lbrace>ct_in_state P and (\<lambda>s. x \<noteq> cur_thread s \<or> P Inactive)\<rbrace>
   cancel_signal x ntfnptr
   \<lbrace>\<lambda>rv. ct_in_state P:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding cancel_signal_def
  by (wpsimp wp: set_thread_state_ct_st hoare_vcg_if_lift2 hoare_vcg_imp_lift get_simple_ko_wp
                    reply_unlink_tcb_ct_in_state_weak get_ep_queue_wp get_blocking_object_wp
                    hoare_vcg_disj_lift hoare_vcg_all_lift get_sk_obj_ref_wp gts_wp)

lemma cancel_ipc_ct_in_state:
  "\<lbrace> ct_in_state P and (\<lambda>s. ipc_queued_thread x s \<longrightarrow> x = cur_thread s \<longrightarrow> P Inactive)\<rbrace>
   cancel_ipc x
   \<lbrace>\<lambda>rv. ct_in_state P:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding cancel_ipc_def
  apply (wpsimp wp: blocked_cancel_ipc_ct_in_state reply_remove_tcb_ct_in_state cancel_signal_ct_in_state
                     hoare_vcg_imp_lift' thread_set_ct_in_state gts_wp)
  by (auto simp: tcb_at_kh_simps pred_map_eq_normalise vs_all_heap_simps)

(* FIXME: move *)
lemma if_cond_then_disj_strg:
  "if A then C else B \<Longrightarrow> A \<or> B"
  by (simp split: if_split_asm)

lemma suspend_ct_in_state:
  "\<lbrace>\<lambda>s. if x = cur_thread s then P Inactive else ct_in_state P s \<and> ct_not_blocked s\<rbrace>
   suspend x
   \<lbrace>\<lambda>rv. ct_in_state P:: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: suspend_def update_restart_pc_def)
  apply (rule hoare_seq_ext[rotated, where A=A and B="\<lambda>_. A" for A])
   apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' cancel_ipc_ct_in_state)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift set_thread_state_ct_st
                    set_tcb_obj_ref_ct_in_state get_tcb_obj_ref_wp |
        strengthen if_cond_then_disj_strg)+
  done

lemma install_tcb_frame_cap_cur_sc_chargeable:
  "\<lbrace>invs and cur_sc_chargeable and ct_not_blocked\<rbrace>
      install_tcb_frame_cap t sl buf
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding install_tcb_frame_cap_def
  by (wpsimp wp: cap_delete_cur_sc_chargeable)

lemma tcc_cur_sc_chargeable:
  "\<lbrace>invs and tcb_inv_wf (ThreadControlCaps t sl fh th croot vroot buf)
    and cur_sc_chargeable and ct_not_blocked\<rbrace>
   invoke_tcb (ThreadControlCaps t sl fh th croot vroot buf)
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_cong[cong]
  apply (simp add: split_def cong: option.case_cong)
  apply wp
  \<comment> \<open>install_tcb_cap 2\<close>
       apply (wpsimp wp: install_tcb_frame_cap_cur_sc_chargeable)
      apply (simp)
      \<comment> \<open>install_tcb_cap 1\<close>
      apply (rule hoare_vcg_E_elim, wp install_tcb_cap_cur_sc_chargeable)
      apply (wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                        install_tcb_cap_invs install_tcb_cap_cur_sc_chargeable)
     \<comment> \<open>install_tcb_cap 0\<close>
     apply (simp)
     apply (rule hoare_vcg_E_elim, wp install_tcb_cap_cur_sc_chargeable)
     apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                        install_tcb_cap_invs install_tcb_cap_cur_sc_chargeable
            | strengthen tcb_cap_always_valid_strg
            | wp install_tcb_cap_cte_wp_at_ep)+)[1]
    \<comment> \<open>install_tcb_cap 4\<close>
    apply (simp)
    apply (rule hoare_vcg_E_elim, wp install_tcb_cap_cur_sc_chargeable)
    apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                       install_tcb_cap_invs install_tcb_cap_cur_sc_chargeable
           | strengthen tcb_cap_always_valid_strg
           | wp install_tcb_cap_cte_wp_at_ep)+)[1]
   \<comment> \<open>install_tcb_cap 3\<close>
   apply (simp)
   apply (rule hoare_vcg_E_elim, wp install_tcb_cap_cur_sc_chargeable)
   apply ((wpsimp wp: hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
                      install_tcb_cap_invs install_tcb_cap_cur_sc_chargeable
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

crunches maybe_sched_context_unbind_tcb, maybe_sched_context_bind_tcb, set_priority
         , bind_notification
  for scheduler_act_sane[wp]: scheduler_act_sane
  (wp: crunch_wps simp: crunch_simps)

crunches install_tcb_cap, install_tcb_frame_cap
  for scheduler_act_sane[wp]: "scheduler_act_sane :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps preemption_point_inv ignore: check_cap_at simp: check_cap_at_def crunch_simps)

lemma test_possible_switch_to_scheduler_act_sane':
  "\<lbrace>scheduler_act_sane and (\<lambda>s. st_tcb_at runnable thread s \<longrightarrow> thread \<noteq> cur_thread s)\<rbrace>
   test_possible_switch_to thread
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding test_possible_switch_to_def
  apply (wpsimp wp: possible_switch_to_scheduler_act_sane' is_schedulable_wp)
  by (clarsimp simp: is_schedulable_bool_def2)

lemma restart_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and (\<lambda>s. thread = cur_thread s \<longrightarrow> ct_in_state activatable s)\<rbrace>
   restart thread
   \<lbrace>\<lambda>rv. scheduler_act_sane:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding restart_def
  apply (wpsimp wp: test_possible_switch_to_scheduler_act_sane' gts_wp sts_st_tcb_at_pred
                    hoare_vcg_if_lift2 hoare_vcg_imp_lift maybeM_inv)
  by (clarsimp simp: ct_in_state_def tcb_at_kh_simps vs_all_heap_simps)

lemma invoke_tcb_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_in_state activatable\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>rv. scheduler_act_sane:: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (case_tac iv; simp)
          apply (find_goal \<open>match premises in "_ = CopyRegisters _ _ _ _ _ _ _" \<Rightarrow> \<open>-\<close>\<close>)
          apply (wpsimp wp: hoare_vcg_if_lift2 mapM_x_wp_inv hoare_vcg_imp_lift' suspend_ct_in_state)
          apply (clarsimp split: if_split)
         apply (find_goal \<open>match premises in "_ = NotificationControl _ _" \<Rightarrow> \<open>-\<close>\<close>)
         apply (rename_tac t ntfn)
         apply (case_tac ntfn; wpsimp)
        apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  done

lemma update_time_stamp_bounded_release_time[wp]:
  "\<lbrace>bounded_release_time scp and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. bounded_release_time scp\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac hoare_seq_ext)
   apply wpsimp
  apply (rule_tac Q="valid_machine_time and (bounded_release_time scp and
        (\<lambda>s. cur_time s = prev_time))" in hoare_weaken_pre[rotated])
   apply clarsimp
  apply (rule hoare_strengthen_post)
   apply (rule dmo_getCurrentTime_sp)
   apply wpsimp
  apply (clarsimp simp: vs_all_heap_simps cfg_bounded_release_time_def unat_le_mono)
  done

lemma invoke_domain_no_exception[wp]:
  "\<lbrace>\<top>\<rbrace> invoke_domain thread domain -, \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: invoke_domain_def)

lemma arch_invoke_irq_control_ctE_E[wp]:
  "arch_invoke_irq_control x2
   \<lbrace>ct_not_queued and ct_not_in_release_q and cur_sc_chargeable and scheduler_act_sane:: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: hoare_vcg_conj_lift)

lemma update_time_stamp_valid_sched[wp]:
  "update_time_stamp \<lbrace>valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift_pre_conj[where R=valid_machine_time] simp: valid_sched_def)

lemma reply_push_scheduler_act_sane[wp]:
  "reply_push caller callee reply_ptr can_donate \<lbrace>scheduler_act_sane:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift | safe)+

lemma invoke_tcb_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable and invs and tcb_inv_wf x and ct_not_blocked\<rbrace>
   invoke_tcb x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac x)
  defer 5
  defer 4
    apply wpsimp+
    apply (case_tac x82; wpsimp)
    apply ((wpsimp wp: install_tcb_cap_cur_sc_chargeable)+)[2]
  apply (wpsimp wp: tcc_cur_sc_chargeable[simplified])
  done

lemma cap_revoke_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable
    and invs
    and ct_not_blocked\<rbrace>
   cap_revoke (a, b)
   \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post, rule cap_revoke_preservation2)
    apply (wpsimp wp: preemption_point_inv cap_delete_cur_sc_chargeable)+
     apply (clarsimp simp: ct_in_state_def)+
  done

lemma invoke_cnode_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable
    and invs and ct_not_blocked\<rbrace>
   invoke_cnode x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (wpsimp wp: cap_revoke_cur_sc_chargeable simp: invoke_cnode_def)+
  apply (rule valid_validE_E)
  apply (wpsimp wp: cap_delete_cur_sc_chargeable)+
  done

crunches cancel_badged_sends
  for scheduler_act_sane[wp]: scheduler_act_sane

crunches invoke_cnode
  for scheduler_act_sane[wp]: "scheduler_act_sane :: 'state_ext state \<Rightarrow> _"

lemma invoke_irq_control_cur_sc_chargeable:
  "\<lbrace>cur_sc_chargeable\<rbrace>
   invoke_irq_control x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (case_tac x; wpsimp simp:)

lemma invs_strengthen_cur_sc_tcb_only_sym_bound:
  "cur_sc_tcb_are_bound s \<and> invs s \<Longrightarrow> cur_sc_tcb_only_sym_bound s"
  unfolding cur_sc_tcb_only_sym_bound_def
  apply (clarsimp simp: tcb_at_kh_simps[symmetric] pred_tcb_at_eq_commute)
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
  apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl], clarsimp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma perform_invocation_cur_sc_chargeable:
  "\<lbrace>cur_sc_tcb_are_bound and ct_not_blocked and invs and
    valid_invocation iv\<rbrace>
   perform_invocation a b c iv
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
             apply (wpsimp simp:)
              apply (strengthen strengthen_cur_sc_chargeable)
              apply (wpsimp wp: cur_sc_chargeable_invoke_untypedE_R)
             apply (fastforce intro: invs_strengthen_cur_sc_tcb_only_sym_bound)
            apply wpsimp+
         apply (wpsimp wp: hoare_vcg_E_conj hoare_elim_pred_conjE2 invoke_tcb_cur_sc_chargeable)
         apply (fastforce intro: invs_strengthen_cur_sc_chargeable simp: valid_sched_def)
        apply wpsimp+
      apply (wpsimp wp: invoke_cnode_cur_sc_chargeable invoke_cnode_scheduler_act_sane)
     apply (fastforce intro: invs_strengthen_cur_sc_chargeable simp: valid_sched_def)
    apply (wpsimp wp: invoke_irq_control_cur_sc_chargeable)+
    apply (fastforce intro: invs_strengthen_cur_sc_chargeable)
   apply wpsimp
  apply wpsimp
  apply (fastforce intro: invs_strengthen_cur_sc_chargeable)
  done

(* FIXME: move *)
lemma active_activatable:
  "active st \<Longrightarrow> activatable st"
  by (case_tac st; simp)

lemma handle_invocation_cur_sc_chargeable:
  "\<lbrace>cur_sc_tcb_are_bound and invs and ct_active\<rbrace>
   handle_invocation a b c d x
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wpsimp wp: syscall_valid perform_invocation_cur_sc_chargeable
                    set_thread_state_ct_in_state hoare_drop_imps set_thread_state_runnable_valid_sched)
      apply (rule validE_cases_valid, clarsimp)
      apply (subst validE_R_def[symmetric])
      apply (rule_tac Q'="\<lambda>r s.
             cur_sc_tcb_are_bound s \<and>
             thread = cur_thread s \<and>
             ct_active s \<and>
             invs s \<and> valid_invocation r s" in hoare_post_imp_R[rotated])
       apply (clarsimp)
       apply (intro conjI)
          apply (fastforce simp: ct_in_state_def runnable_eq_active)
         apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
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

lemma handle_event_cur_sc_chargeable:
  "\<lbrace>cur_sc_tcb_are_bound and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   handle_event e
   -, \<lbrace>\<lambda>rv. cur_sc_chargeable :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       apply (rename_tac syscall)
       apply (case_tac syscall; simp)
                 apply (wpsimp simp: handle_send_def handle_call_def
                                 wp: handle_invocation_cur_sc_chargeable check_budget_restart_true
                        | erule active_from_running)+
  done

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

lemma update_sched_context_weak_valid_sched_action':
  "\<lbrace>weak_valid_sched_action
    and K (\<forall>sc. sc_refills (f sc) = sc_refills (sc))
    and K (\<forall>sc. sc_active sc \<longrightarrow> sc_active (f sc))\<rbrace>
      update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp simp: set_object_def wp: get_object_wp update_sched_context_wp)
  apply (clarsimp simp: weak_valid_sched_action_def)
  apply (prop_tac "budget_ready t s";
         clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps split: if_splits)
  apply (prop_tac "t \<noteq> ref"; clarsimp)
  apply (rule_tac x=ref'a in exI)
  by fastforce

lemma update_sched_context_valid_blocked':
  "\<lbrace>valid_blocked and K (\<forall>sc. sc_active sc \<longleftrightarrow> sc_active (f sc))\<rbrace>
     update_sched_context ptr f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: set_object_def wp: get_object_wp update_sched_context_wp)
  apply (clarsimp simp: valid_blocked_defs)
  apply (prop_tac "active_sc_tcb_at t s \<and> pred_map active (tcb_sts_of s) t",
         clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps split: if_splits)
  by fastforce

lemma sc_with_tcb_propE1:
  "P t s
   \<Longrightarrow> (\<forall>tp. bound_sc_tcb_at ((=) (Some scp)) tp s \<longrightarrow> tp = t)
   \<Longrightarrow> sc_with_tcb_prop scp P s"
 by (clarsimp simp: tcb_at_kh_simps pred_map_eq_def)

lemma ct_active_sc_helper:
  "\<And>s. (\<forall>t. t = (cur_thread s) \<longrightarrow> P (active_sc_tcb_at t s)) \<Longrightarrow>
   P (active_sc_tcb_at (cur_thread s) s)"
  by simp

lemma refill_budget_check_round_robin_released_ipc_queues:
  "\<lbrace>released_ipc_queues
    and valid_machine_time
    and active_sc_valid_refills
    and cur_sc_not_blocked\<rbrace>
   refill_budget_check_round_robin usage
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  supply if_split[split del]
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: set_refills_released_ipc_queues is_round_robin_wp simp: cur_sc_not_blocked_def)

(* FIXME RT: move *)
lemma released_imp_active: "released_sc_tcb_at t s \<Longrightarrow> active_sc_tcb_at t s"
  by (fastforce simp: pred_map2'_pred_maps elim!: pred_map_weakenE)

lemma refill_budget_check_released_ipc_queues:
  "\<lbrace>released_ipc_queues
    and valid_machine_time
    and active_sc_valid_refills
    and cur_sc_not_blocked\<rbrace>
   refill_budget_check usage
   \<lbrace>\<lambda>_. released_ipc_queues\<rbrace>"
  supply if_split[split del]
  unfolding refill_budget_check_def
  by (wpsimp wp: set_refills_released_ipc_queues is_round_robin_wp simp: cur_sc_not_blocked_def)

lemma charge_budget_valid_blocked[wp]:
  "\<lbrace>valid_blocked_except_set S\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_blocked_except_set S:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: reschedule_required_valid_blocked end_timeslice_valid_blocked
                 assert_inv gts_wp is_schedulable_wp')

lemma charge_budget_valid_release_q:
  "\<lbrace>\<lambda>s. valid_release_q s \<and> ct_not_in_release_q s \<and> cur_sc_chargeable s
        \<and> heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s)\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply wpsimp
              apply (wpsimp wp: end_timeslice_valid_release_q)
             apply (wpsimp wp: assert_inv)
            apply (wpsimp wp: gts_wp is_schedulable_wp')+
       apply (rule_tac Q="\<lambda>_ s. valid_release_q s \<and> cur_sc_chargeable s
                                 \<and> heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s)"
              in hoare_strengthen_post[rotated])
        apply (clarsimp simp: tcb_at_kh_simps ct_in_state_def runnable_eq_active
                       split: if_splits)
       apply (wpsimp wp: sc_consumed_add_invs)
      apply (wpsimp wp: refill_budget_check_round_robin_valid_release_q
                        refill_budget_check_valid_release_q)+
  apply (subgoal_tac "sc_not_in_release_q (cur_sc s) s ", simp)
  apply (intro conjI impI allI)
  apply (clarsimp simp: cur_sc_chargeable_def)
  apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
   apply (drule_tac x=t in spec)+
   apply (clarsimp simp: pred_map_simps, fastforce)
  apply (clarsimp simp: valid_release_q_def in_queue_2_def)
  done

lemma charge_budget_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_sane and cur_sc_chargeable\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply wpsimp
            apply (wpsimp wp: gts_wp is_schedulable_wp')+
       apply (rule_tac Q="\<lambda>ya s.
                (if (pred_map runnable (tcb_sts_of s) (cur_thread s) \<and> ct_not_in_release_q s \<and> active_sc_tcb_at (cur_thread s) s)
                 then True
                 else valid_sched_action s)" in hoare_strengthen_post[rotated])
        apply (clarsimp simp: tcb_at_kh_simps ct_in_state_def runnable_eq_active
                       split: if_splits)
       apply (wpsimp wp: hoare_vcg_if_lift_strong sc_consumed_add_invs)
      apply (wpsimp wp: hoare_vcg_if_lift_strong)
          apply (rule_tac hoare_strengthen_post[rotated], erule ct_active_sc_helper)
          apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (rule_tac hoare_strengthen_post[rotated], erule ct_active_sc_helper)
         apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
        apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift')
          apply (rule_tac hoare_strengthen_post[rotated], erule ct_active_sc_helper)
          apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift')
         apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
       apply wpsimp
      apply (wpsimp wp: refill_budget_check_round_robin_valid_sched_action_act_not
                        refill_budget_check_valid_sched_action_act_not)
     apply (wpsimp wp: is_round_robin_wp)+
  apply (clarsimp simp: valid_sched_def valid_sched_action_def)
  apply (subgoal_tac "sc_scheduler_act_not (cur_sc s) s", simp)
  apply (intro conjI impI allI)
  apply (clarsimp simp: cur_sc_chargeable_def scheduler_act_sane_def)
  apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
  apply (drule_tac x=t in spec)+
  apply (fastforce simp: pred_map_simps)
  apply (clarsimp simp:  weak_valid_sched_action_def in_queue_2_def)
  done

(* FIXME: why are these three not crunchable? *)
lemma charge_budget_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain \<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. ct_in_cur_domain :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma charge_budget_valid_idle_etcb[wp]:
  "\<lbrace>valid_idle_etcb\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_idle_etcb :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma charge_budget_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q \<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. ct_not_in_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunches charge_budget
  for valid_machine_time[wp]: "valid_machine_time :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

lemma charge_budget_released_ipc_queues:
  "\<lbrace>released_ipc_queues
    and valid_machine_time
    and cur_sc_not_blocked
    and active_sc_valid_refills\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. released_ipc_queues :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply (wpsimp wp: end_timeslice_released_ipc_queues assert_inv gts_wp is_schedulable_wp')
       apply (rule_tac Q="\<lambda>_. released_ipc_queues" in hoare_strengthen_post[rotated]
              , clarsimp simp: tcb_at_kh_simps ct_in_state_def runnable_eq_active split: if_splits)
       apply (wpsimp wp: refill_budget_check_round_robin_released_ipc_queues
                         refill_budget_check_released_ipc_queues
                         is_round_robin_wp' get_sched_context_wp gets_wp)+
  done

lemma ct_not_blocked_cur_sc_not_blocked:
  "cur_sc_chargeable s \<Longrightarrow> ct_not_blocked s \<Longrightarrow> cur_sc_not_blocked s"
  unfolding cur_sc_not_blocked_def cur_sc_chargeable_def
  apply (clarsimp)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in spec)
  by (auto simp: ct_in_state_def tcb_at_kh_simps vs_all_heap_simps)

lemma charge_budget_valid_ready_qs:
  "\<lbrace>valid_ready_qs
    and released_ipc_queues
    and valid_machine_time
    and active_sc_valid_refills
    and valid_sched_action
    and scheduler_act_sane
    and ct_not_queued and scheduler_act_sane
    and cur_sc_chargeable
    and cur_sc_not_blocked\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_ready_qs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply wpsimp
              apply (wpsimp wp: end_timeslice_valid_ready_qs)
             apply (wpsimp wp: assert_inv)
            apply (wpsimp wp: gts_wp is_schedulable_wp')+
       apply (rule_tac Q="\<lambda>_ s. ct_not_queued s \<and> cur_sc_chargeable s \<and> valid_ready_qs s
                                 \<and> released_ipc_queues s \<and> valid_sched_action s \<and> scheduler_act_sane s"
              in hoare_strengthen_post[rotated])
        apply (clarsimp simp: tcb_at_kh_simps ct_in_state_def runnable_eq_active
                       split: if_splits)
       apply wpsimp
      apply (wpsimp wp: refill_budget_check_round_robin_valid_ready_qs_not_queued
                        refill_budget_check_round_robin_released_ipc_queues
                        refill_budget_check_round_robin_valid_sched_action_act_not
                        refill_budget_check_valid_ready_qs_not_queued
                        refill_budget_check_released_ipc_queues
                        refill_budget_check_valid_sched_action_act_not)
     apply (wpsimp wp: is_round_robin_wp)+
  apply (subgoal_tac "sc_not_in_ready_q (cur_sc s) s \<and> sc_scheduler_act_not (cur_sc s) s", simp)
  apply (intro conjI impI allI)
   apply (clarsimp simp: cur_sc_chargeable_def)
   apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
    apply (drule_tac x=t in spec)+
    apply (clarsimp simp: pred_map_simps, fastforce)
   apply (clarsimp simp: valid_ready_qs_def in_queue_2_def in_ready_q_def)
  apply (clarsimp simp: cur_sc_chargeable_def scheduler_act_sane_def)
  apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
   apply (drule_tac x=t in spec)+
   apply (fastforce simp: pred_map_simps)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def)
  done

lemma charge_budget_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and K (unat consumed + unat MAX_SC_PERIOD \<le> unat max_time)
    and current_time_bounded 2
    and (\<lambda>s. (\<forall>sc. (\<exists>n. kheap s (cur_sc s) = Some (SchedContext sc n)) \<longrightarrow>
                    (sc_refill_ready (cur_time s) sc \<longrightarrow>
                     r_amount (refill_hd sc) < consumed) \<longrightarrow>
                    cur_sc_offset_ready consumed s))\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. active_sc_valid_refills :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp: charge_budget_def)
  apply (wpsimp wp: hoare_drop_imp
                    refill_budget_check_round_robin_active_sc_valid_refills
                    refill_budget_check_active_sc_valid_refills)
  apply (erule current_time_bounded_strengthen, simp)
  done

lemma end_timeslice_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> (can_timeout \<longrightarrow> active_if_bound_sc_tcb_at (cur_thread s) s)\<rbrace>
   end_timeslice can_timeout
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def by (wpsimp wp: handle_timeout_active_reply_scs thread_get_wp')

lemma refill_budget_check_round_robin_cur_sc_active[wp]:
  "refill_budget_check_round_robin consumed \<lbrace>cur_sc_active\<rbrace>"
  by (wpsimp wp: refill_budget_check_round_robin_sc_refills_update_unspecified
           simp: active_reply_scs_defs)

lemma refill_budget_check_cur_sc_active[wp]:
  "refill_budget_check consumed \<lbrace>cur_sc_active\<rbrace>"
  by (wpsimp wp: refill_budget_check_sc_refills_update_unspecified
           simp: active_reply_scs_defs)

lemma charge_budget_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> (can_timeout \<longrightarrow> cur_sc_tcb_are_bound s \<longrightarrow> cur_sc_active s)\<rbrace>
   charge_budget consumed can_timeout
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (repeat 5 \<open>rule hoare_seq_ext_skip, solves \<open>wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_disj_lift\<close>, simp?\<close>)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>, simp?)+
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp wp: end_timeslice_active_reply_scs)
  by (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)

lemma charge_budget_ready_or_release:
  "\<lbrace>ready_or_release and valid_ready_qs and ct_not_in_release_q and ct_not_queued
    and cur_sc_chargeable\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. ready_or_release :: 'state_ext state \<Rightarrow> _ \<rbrace>"
  apply (clarsimp simp: charge_budget_def when_def)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>))+
  apply (rule hoare_seq_ext_skip)
   apply (rule hoare_if)
    apply (wpsimp wp: refill_budget_check_round_robin_valid_ready_qs_not_queued)
    apply (clarsimp simp: cur_sc_chargeable_def vs_all_heap_simps pred_map_simps)
    apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
     apply (fastforce simp: cur_sc_chargeable_def vs_all_heap_simps pred_map_simps)
    apply (clarsimp simp: valid_ready_qs_def in_queue_2_def in_ready_q_def)
   apply (wpsimp wp: refill_budget_check_valid_ready_qs_not_queued)
   apply (clarsimp simp: cur_sc_chargeable_def vs_all_heap_simps pred_map_simps)
   apply (subgoal_tac "pred_map runnable (tcb_sts_of s) t")
    apply (fastforce simp: cur_sc_chargeable_def vs_all_heap_simps pred_map_simps)
   apply (clarsimp simp: valid_ready_qs_def in_queue_2_def in_ready_q_def)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>))+
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp\<close>)+
  by wpsimp

lemma charge_budget_valid_sched:
  "\<lbrace>valid_sched
    and (\<lambda>s. heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s))
    and ct_not_in_release_q
    and ct_not_queued
    and scheduler_act_sane
    and cur_sc_chargeable
    and cur_sc_not_blocked
    and current_time_bounded 2
    and K (unat consumed + unat MAX_SC_PERIOD \<le> unat max_time)
    and cur_sc_active
    and (\<lambda>s. (\<forall>sc. (\<exists>n. kheap s (cur_sc s) = Some (SchedContext sc n)) \<longrightarrow>
                    (sc_refill_ready (cur_time s) sc \<longrightarrow>
                     r_amount (refill_hd sc) < consumed) \<longrightarrow>
                    cur_sc_offset_ready consumed s))\<rbrace>
   charge_budget consumed canTimeout
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: charge_budget_valid_ready_qs charge_budget_active_sc_valid_refills
                 charge_budget_valid_release_q
                 charge_budget_valid_sched_action
                 charge_budget_released_ipc_queues
                 charge_budget_active_reply_scs
                 charge_budget_ready_or_release)

lemma check_budget_valid_ready_qs:
  "\<lbrace>valid_ready_qs and released_ipc_queues and valid_machine_time and valid_sched_action
    and ct_not_queued
    and active_sc_valid_refills
    and scheduler_act_sane and cur_sc_chargeable
    and cur_sc_not_blocked\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_ready_qs::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: get_sched_context_wp charge_budget_valid_ready_qs
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)

lemma check_budget_valid_release_q:
  "\<lbrace>valid_release_q
    and (\<lambda>s. heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s))
    and ct_not_in_release_q
    and cur_sc_chargeable\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_release_q::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: get_sched_context_wp charge_budget_valid_release_q
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)

lemma check_budget_released_ipc_queues:
  "\<lbrace>released_ipc_queues
    and valid_machine_time
    and active_sc_valid_refills
    and cur_sc_not_blocked\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. released_ipc_queues::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: get_sched_context_wp charge_budget_released_ipc_queues
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)

lemma check_budget_active_sc_valid_refills:
  "\<lbrace>active_sc_valid_refills
    and current_time_bounded 2
    and consumed_time_bounded
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. active_sc_valid_refills::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  apply (wpsimp wp: get_sched_context_wp charge_budget_active_sc_valid_refills
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)
  apply (fastforce elim: consumed_time_bounded_helper current_time_bounded_strengthen)
  done

crunches check_budget
  for ct_not_in_q[wp]: "ct_not_in_q ::'state_ext state \<Rightarrow> _"
  and ct_in_cur_domain[wp]: "ct_in_cur_domain ::'state_ext state \<Rightarrow> _"
  and valid_blocked[wp]: "valid_blocked_except_set S ::'state_ext state \<Rightarrow> _"
  and valid_idle_etcb[wp]: "valid_idle_etcb ::'state_ext state \<Rightarrow> _"
  and valid_machine_time[wp]: "valid_machine_time ::'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

lemma check_budget_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_sane and cur_sc_chargeable\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_sched_action::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: get_sched_context_wp charge_budget_valid_sched_action
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)

lemma check_budget_active_reply_scs:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> (cur_sc_tcb_are_bound s \<longrightarrow> cur_sc_active s)\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. active_reply_scs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def by (wpsimp wp: charge_budget_active_reply_scs)

lemma check_budget_ready_or_release:
  "\<lbrace>ready_or_release and valid_ready_qs and ct_not_in_release_q and ct_not_queued
    and cur_sc_chargeable\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. ready_or_release :: 'state_ext state \<Rightarrow> _ \<rbrace>"
  unfolding check_budget_def by (wpsimp wp: charge_budget_ready_or_release)

lemma check_budget_valid_sched:
  "\<lbrace>valid_sched
    and (\<lambda>s. heap_refs_retract_at (tcb_scps_of s) (sc_tcbs_of s) (cur_thread s))
    and ct_not_in_release_q
    and ct_not_queued
    and scheduler_act_sane
    and cur_sc_chargeable
    and cur_sc_not_blocked
    and current_time_bounded 2
    and consumed_time_bounded
    and (\<lambda>s. cur_sc_tcb_are_bound s \<longrightarrow> cur_sc_active s)
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: valid_sched_def)
  by (wpsimp wp: check_budget_valid_ready_qs check_budget_active_sc_valid_refills
                 check_budget_valid_release_q
                 check_budget_valid_sched_action
                 check_budget_released_ipc_queues
                 check_budget_active_reply_scs
                 check_budget_ready_or_release)

lemma tcb_sched_dequeue_valid_blocked_except_set:
  "\<lbrace>\<lambda>s. if not_queued tcb_ptr s then valid_blocked_except_set {tcb_ptr} s else valid_blocked s\<rbrace>
   tcb_sched_action tcb_sched_dequeue tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except_set {tcb_ptr} s\<rbrace>"
  unfolding tcb_sched_action_def
  apply (wpsimp wp: set_tcb_queue_wp simp: thread_get_def)
  apply (clarsimp simp: valid_blocked_defs tcb_sched_dequeue_def obj_at_def split: if_splits)
   apply (drule_tac x=t in spec; clarsimp )
   apply (case_tac "not_queued t s"; clarsimp)
   apply (clarsimp simp: not_queued_def in_ready_q_def not_queued_2_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply (drule_tac x=p in spec)
   apply (fastforce simp: tcb_sched_dequeue_def split: if_splits)
  apply (clarsimp simp: not_queued_2_def valid_blocked_defs in_ready_q_def)
  apply (drule_tac x=t in spec; clarsimp )
  apply (auto simp: tcb_sched_dequeue_def split: if_splits)
  done

lemma tcb_release_remove_valid_blocked:
  "\<lbrace>\<lambda>s. if not_in_release_q tcb_ptr s then valid_blocked_except tcb_ptr s else valid_blocked s\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv s. valid_blocked_except tcb_ptr s\<rbrace>"
  unfolding tcb_release_remove_def
  apply (wpsimp)
  apply (clarsimp simp: valid_blocked_defs obj_at_def split: if_splits)
   apply (fastforce simp: in_release_q_def in_ready_q_def tcb_sched_act_in_queues_2_simps)
  apply (fastforce simp: in_release_q_def in_ready_q_def tcb_sched_act_in_queues_2_simps)
  done

lemma tcb_release_remove_sc_tcb_at[wp]:
  "\<lbrace>sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr\<rbrace>
   tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>rv. sc_tcb_sc_at (\<lambda>a. a = Some tcb_ptr) sc_ptr\<rbrace>"
   unfolding tcb_release_remove_def
   by wpsimp

lemma update_sched_context_tcb_ready_time:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s) \<and> (\<forall>x. sc_refills (f x) = sc_refills x)\<rbrace>
   update_sched_context sc_ptr f
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def
                  wp: get_object_wp split_del: if_split)
  by (auto simp: vs_all_heap_simps tcb_ready_times_defs obj_at_def opt_map_def map_project_def
                 map_join_def tcb_scps_of_tcbs_def tcbs_of_kh_def sc_refill_cfgs_of_scs_def
                 scs_of_kh_def
          split: option.split)

lemma active_sc_tcb_at_update_sched_context_no_change:
  "\<forall>x. (sc_active (f x)) = (sc_active x) \<Longrightarrow>
    \<forall>x. sc_refills (f x) = sc_refills x
   \<Longrightarrow> \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> update_sched_context sc_ptr f \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: valid_sched_lift set_object_wp get_object_wp
              simp: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (intro conjI impI allI)
   apply wpsimp
  apply (erule_tac P=P in back_subst, force)
  done

lemma update_sched_context_valid_refills_indep:
  "\<forall>sc. sc_refill_cfg_of (f sc) = sc_refill_cfg_of sc \<Longrightarrow>
   update_sched_context sc_ptr f \<lbrace>valid_refills t\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_def)
  done

lemma charge_budget_valid_sched_misc[wp]:
  "charge_budget consumed canTimeout
   \<lbrace>\<lambda>s::'state_ext state. P (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                            (last_machine_time_of s) (etcbs_of s) \<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp)

lemma check_budget_valid_sched_misc[wp]:
  "check_budget
   \<lbrace>\<lambda>s::'state_ext state. P (cur_sc s) (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
                            (last_machine_time_of s) (etcbs_of s)\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: hoare_drop_imp)

lemma pst_vs_for_invoke_sched_control_configure:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and st_tcb_at runnable target
    and (\<lambda>s. target \<noteq> idle_thread s)
    and (\<lambda>s. not_in_release_q target s \<longrightarrow> released_if_bound_sc_tcb_at target s)\<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wp possible_switch_to_valid_sched_strong)
  apply (clarsimp simp: valid_sched_def )
  apply (intro conjI; intro allI impI)
   apply (clarsimp simp:  released_sc_tcb_at_def tcb_at_kh_simps pred_map_simps)
  apply (erule valid_blockedE', clarsimp)
  apply (clarsimp simp: in_release_queue_def not_in_release_q_def valid_blocked_thread_def
                        vs_all_heap_simps)
  done

lemma valid_blocked_except_set_in_ready_q:
  "\<lbrakk>valid_blocked_except tcbptr s; in_ready_q tcbptr s\<rbrakk> \<Longrightarrow> valid_blocked s"
  apply (clarsimp simp: valid_blocked_defs)
  apply (case_tac "t = tcbptr")
   apply (fastforce iff: not_not_in_eq_in[symmetric])
  apply (drule_tac x=t in spec; simp)
  done

lemma valid_blocked_except_cur_thread:
  "valid_blocked_except_set {cur_thread s} s = valid_blocked s"
  using valid_blocked_defs by simp

lemma refill_budget_check_sc_refill_max_sc_at:
  "refill_budget_check usage \<lbrace>sc_refill_max_sc_at P sc_ptr\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: update_sched_context_wp set_refills_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
              simp: is_round_robin_def sc_at_pred_n_def obj_at_def
                    refill_budget_check_def refill_full_def refill_ready_def
      | intro conjI impI)+

lemma refill_budget_check_round_robin_sc_refill_max_sc_at:
  "refill_budget_check_round_robin usage \<lbrace>sc_refill_max_sc_at P sc_ptr\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: update_sched_context_wp set_refills_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
              simp: refill_budget_check_round_robin_def is_round_robin_def sc_at_pred_n_def
                    obj_at_def refill_full_def refill_ready_def
      | intro conjI impI)+

lemma commit_time_sc_refill_max_sc_at:
  "commit_time \<lbrace>\<lambda>s. sc_refill_max_sc_at P sc_ptr s\<rbrace>"
  unfolding commit_time_def commit_domain_time_def
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp?\<close>)+
  apply (clarsimp simp: when_def)
  apply (intro conjI impI allI; (clarsimp simp: bind_assoc)?)

     \<comment> \<open>0 < consumed \<and> 0 < sc_refill_max sc\<close>
     apply (rule hoare_seq_ext_skip, solves \<open>wpsimp?\<close>)+
     apply clarsimp
     apply (intro conjI impI)
      apply (rule hoare_seq_ext_skip
             , wpsimp wp: refill_budget_check_round_robin_sc_refill_max_sc_at)
      apply (wpsimp wp: update_sched_context_wp simp: sc_at_pred_n_def obj_at_def)
     apply (rule hoare_seq_ext_skip, wpsimp wp: refill_budget_check_sc_refill_max_sc_at)
     apply (wpsimp wp: update_sched_context_wp simp: sc_at_pred_n_def obj_at_def)

     \<comment> \<open>remaining cases\<close>
    apply (wpsimp wp: update_sched_context_wp simp: sc_at_pred_n_def obj_at_def)+
  done

crunches tcb_release_remove, tcb_sched_action
  for sc_refill_max_sc_at[wp]: "sc_refill_max_sc_at P sc_ptr"

definition is_next_time where
  "is_next_time a s \<equiv> \<exists>b. (a, b) \<in> fst (do_machine_op getCurrentTime s)"

definition pred_next_time where
  "pred_next_time P s \<equiv> \<forall>a. is_next_time a s \<longrightarrow> P a"

lemma pred_next_time_irq_state_independent_Aff[simp]:
  "pred_next_time P (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = pred_next_time P s"
  by (clarsimp simp: pred_next_time_def is_next_time_def do_machine_op_def in_monad
                        ARM.getCurrentTime_def select_f_def)

lemma cur_sc_offset_ready_weaken_zero[elim!]:
  "cur_sc_offset_ready k s \<Longrightarrow> cur_sc_offset_ready 0 s"
  by (clarsimp simp: cur_sc_offset_ready_def pred_map_simps)

(* FIXME: move *)
abbreviation next_time_bounded where
  "next_time_bounded k s \<equiv> pred_next_time (current_time_bounded_2 k) s"

lemma pred_next_time_strengthen:
  "pred_next_time P s \<Longrightarrow> (\<forall>a. P a \<longrightarrow> Q a) \<Longrightarrow> pred_next_time Q s"
  by (clarsimp simp: pred_next_time_def)

lemma next_time_bounded_weaken:
  "next_time_bounded k s
   \<Longrightarrow> n \<le> k
   \<Longrightarrow> next_time_bounded n s"
  apply (erule pred_next_time_strengthen, clarsimp)
  by (erule (1) current_time_bounded_strengthen)

lemma next_time_bounded_current_time_bounded:
  "next_time_bounded k s \<Longrightarrow> valid_machine_time s \<Longrightarrow> current_time_bounded k s"
  apply (clarsimp simp: pred_next_time_def current_time_bounded_def valid_machine_time_def is_next_time_def)
  apply (clarsimp simp: do_machine_op_def ARM.getCurrentTime_def in_monad select_f_def)
  apply (erule order_trans[rotated])
  apply (clarsimp simp: min_def; intro allI impI conjI)
   apply (clarsimp simp: word_le_nat_alt[symmetric])
   apply (erule order_trans, erule order_trans)
   apply (subst word_of_nat_minus)
    apply (rule_tac y="unat max_time" in order_trans)
     apply (clarsimp simp: word_le_nat_alt[symmetric])
    apply (clarsimp simp: max_word_def)
   apply (subst diff_conv_add_uminus)
   apply (subst max_word_minus[symmetric], clarsimp simp: max_word_def)
  apply (clarsimp simp: word_le_nat_alt[symmetric] not_le)
  apply (erule order_trans, overflow_hammer)
  apply (rule order_trans)
   apply (rule add_left_mono, rule unat_of_nat_closure)
  apply (rule order_trans)
   apply (erule order.strict_implies_order, clarsimp simp: max_word_def)
  done

lemma next_time_bounded_weaken1:
  "next_time_bounded 1 s \<Longrightarrow> pred_next_time (\<lambda>x. unat x + unat MAX_SC_PERIOD \<le> unat max_time) s"
  by (erule pred_next_time_strengthen, clarsimp simp: current_time_bounded_def)

lemma current_time_bounded_weaken1:
  "current_time_bounded 2 s \<Longrightarrow> 2 * unat MAX_SC_PERIOD \<le> unat max_time"
  by (clarsimp simp: current_time_bounded_def)

lemmas next_time_bounded_weaken2 = next_time_bounded_current_time_bounded[THEN current_time_bounded_weaken1]

lemma current_time_bounded1_drop_WCET:
  "current_time_bounded 1 s \<Longrightarrow> unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time"
  by (clarsimp simp: current_time_bounded_def)

lemma current_time_bounded_drop_WCET:
  "current_time_bounded k s \<Longrightarrow> unat (cur_time s) + k * unat MAX_SC_PERIOD \<le> unat max_time"
  by (clarsimp simp: current_time_bounded_def)

abbreviation (input) iscc_valid_sched_predicate where
  "iscc_valid_sched_predicate sc_ptr tcb_ptr mrefills budget s \<equiv>
    valid_sched_except_blocked s
    \<and> valid_blocked_except tcb_ptr s
    \<and> MIN_REFILLS \<le> mrefills
    \<and> MIN_SC_BUDGET \<le> budget
    \<and> schact_is_rct s
    \<and> ready_or_release s
    \<and> invs s
    \<and> sc_ptr \<noteq> idle_sc_ptr
    \<and> ct_not_in_release_q s
    \<and> ct_not_queued s"

(* FIXME: move *)
lemma consumed_time_bounded_trivial[simp]:
  "consumed_time_bounded_2 0 k = True"
  by (clarsimp simp: consumed_time_bounded_def)

crunches commit_time
  for consumed_time_bounded[wp]: consumed_time_bounded

lemma tcb_release_remove_cur_sc_in_release_q_imp_zero_consumed[wp_unsafe]:
  "tcb_release_remove tcb_ptr \<lbrace>cur_sc_in_release_q_imp_zero_consumed\<rbrace>"
  apply (wpsimp wp: tcb_release_remove_wp)
  apply (case_tac "t = tcb_ptr"; clarsimp simp: in_queue_2_def tcb_sched_dequeue_def)
  done

lemma ct_not_in_release_q_cur_sc_in_release_q_imp_zero_consumed:
  "schact_is_rct s \<Longrightarrow> invs s \<Longrightarrow> ct_not_in_release_q s \<Longrightarrow> cur_sc_in_release_q_imp_zero_consumed s"
  apply (frule invs_cur_sc_tcb)
  apply (clarsimp simp: schact_is_rct_def cur_sc_tcb_def obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (frule (2) heap_refs_retract_eq[OF invs_retract_tcb_scps], clarsimp)
  done

lemma refill_budget_check_round_robin_is_active_sc[wp]:
  "refill_budget_check_round_robin d \<lbrace>is_active_sc scp\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  by (wpsimp wp: valid_sched_wp is_round_robin_wp)

lemma refill_budget_check_is_active_sc[wp]:
  "refill_budget_check d \<lbrace>is_active_sc scp\<rbrace>"
  unfolding refill_budget_check_def
  by (wpsimp wp: valid_sched_wp is_round_robin_wp)

lemma commit_time_is_active_sc[wp]:
  "commit_time \<lbrace>is_active_sc scp\<rbrace>"
  unfolding commit_time_def
  by (wpsimp wp: hoare_drop_imp)

lemma commit_time_cur_sc_active[wp]:
  "commit_time \<lbrace>cur_sc_active\<rbrace>"
  by (rule cur_sc_active_lift; wpsimp)

lemma refill_new_active_reply_scs[wp]:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> active_sc max_refills\<rbrace>
   refill_new sc_ptr max_refills budget period
   \<lbrace>\<lambda>_. active_reply_scs\<rbrace>"
  apply (rule active_reply_scs_lift_pre_conj, rule active_reply_sc_at_lift_pre_conj, wpsimp)
  unfolding refill_new_def2
  apply (wpsimp wp: valid_sched_wp)
  by (clarsimp simp: heap_upd_def vs_all_heap_simps)

lemma refill_update_active_reply_scs[wp]:
  "\<lbrace>\<lambda>s. active_reply_scs s \<and> active_sc new_max_refills\<rbrace>
   refill_update sc_ptr new_period new_budget new_max_refills
   \<lbrace>\<lambda>_. active_reply_scs\<rbrace>"
  apply (rule active_reply_scs_lift_pre_conj, rule active_reply_sc_at_lift_pre_conj, wpsimp)
  unfolding refill_update_def2
  apply (wpsimp wp: valid_sched_wp)
  by (clarsimp simp: heap_upd_def vs_all_heap_simps)

lemma invoke_sched_control_configure_valid_sched:
  "\<lbrace>valid_sched
    and valid_sched_control_inv iv and schact_is_rct and ready_or_release and invs
    and ct_not_in_release_q and ct_released and ct_not_queued
    and current_time_bounded 2
    and consumed_time_bounded
    and cur_sc_active
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
     invoke_sched_control_configure iv
   \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split[split del]
  apply (simp add: invoke_sched_control_configure_def)
  apply (cases iv; simp)
  apply (rename_tac sc_ptr budget period mrefills badge)
  apply (rule validE_valid)
  apply (rule liftE_wp)

  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp simp: obj_at_def)
   apply (rule_tac B="\<lambda>rv s. valid_sched s
                             \<and> MIN_REFILLS \<le> mrefills
                             \<and> MIN_SC_BUDGET \<le> budget
                             \<and> budget \<le> period
                             \<and> ex_nonz_cap_to sc_ptr s
                             \<and> schact_is_rct s
                             \<and> ready_or_release s
                             \<and> invs s
                             \<and> sc_ptr \<noteq> idle_sc_ptr
                             \<and> ct_not_in_release_q s
                             \<and> ct_not_queued s
                             \<and> cur_sc_active s
                             \<and> sc_refill_max_sc_at (\<lambda>rm. rm = sc_refill_max sc) sc_ptr s
                             \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s
                             \<and> period \<le> MAX_SC_PERIOD \<and> cur_sc_offset_ready (consumed_time s) s
                             \<and> cur_sc_in_release_q_imp_zero_consumed s
                             \<and> current_time_bounded 2 s \<and> consumed_time_bounded s"
             in hoare_seq_ext[rotated])
   apply (wpsimp wp: update_sc_badge_invs')
    apply (wpsimp wp: update_sched_context_wp)
   apply clarsimp
   apply (intro conjI impI)
    apply (frule invs_valid_global_refs)
    apply (frule invs_valid_objs)
    using idle_sc_no_ex_cap apply blast
   apply (intro conjI impI allI)
      apply (simp add: sc_at_pred_n_def obj_at_def)
     apply (simp add: sc_at_pred_n_def obj_at_def)
    apply (clarsimp simp: cur_sc_offset_ready_def obj_at_kh_kheap_simps pred_map_eq_normalise
                          vs_all_heap_simps
                   split: if_splits)
   apply (subgoal_tac "cur_sc_in_release_q_imp_zero_consumed s")
   apply (clarsimp simp: vs_all_heap_simps split: if_splits)
   apply (erule ct_not_in_release_q_cur_sc_in_release_q_imp_zero_consumed; clarsimp)

  apply (case_tac "sc_tcb sc = None")
   apply (clarsimp simp: bind_assoc valid_sched_def)
   apply (wpsimp wp: refill_new_valid_release_q refill_new_valid_ready_qs
                     refill_new_schedulable_ipc_queues refill_new_valid_sched_action
                     refill_new_valid_blocked_no_sc_tcb refill_new_active_sc_valid_refills)
   apply (frule invs_sym_refs)
   apply (clarsimp simp: active_sc_def cong: conj_cong)
   apply (intro conjI)
         using MIN_BUDGET_le_MIN_SC_BUDGET apply simp
        apply (simp add: MIN_REFILLS_def)
       apply (clarsimp simp: vs_all_heap_simps obj_at_def)
       apply (rename_tac sc tcb_ptr n tcb)
       apply (clarsimp simp add: sc_at_pred_n_def obj_at_def)
       apply (frule_tac tp=tcb_ptr and tcb=tcb in sym_ref_tcb_sc; blast?)
       apply simp
      apply (clarsimp simp: schact_is_rct_simple)
     apply (clarsimp simp add: sc_at_pred_n_def obj_at_def)
    apply (clarsimp simp: current_time_bounded_def)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def split: if_splits)

  \<comment> \<open>\<exists>y. sc_tcb sc = Some y\<close>
  apply (clarsimp simp: bind_assoc)
  apply (rename_tac tcb_ptr)
  apply (rule_tac B="\<lambda>rv s. iscc_valid_sched_predicate sc_ptr tcb_ptr mrefills budget s
                            \<and> budget \<le> period \<and> period \<le> MAX_SC_PERIOD \<and> current_time_bounded 2 s
                            \<and> ex_nonz_cap_to sc_ptr s \<and> consumed_time_bounded s
                            \<and> sc_refill_max_sc_at (\<lambda>rm. rm = sc_refill_max sc) sc_ptr s
                            \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s
                            \<and> not_in_release_q tcb_ptr s \<and> cur_sc_offset_ready (consumed_time s) s
                            \<and> cur_sc_in_release_q_imp_zero_consumed s \<and> cur_sc_active s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: tcb_release_remove_valid_sched_except_blocked tcb_release_remove_valid_blocked
                     tcb_release_remove_ready_or_release
                     hoare_vcg_conj_lift tcb_release_remove_cur_sc_in_release_q_imp_zero_consumed)
   apply (clarsimp simp: valid_sched_valid_sched_except_blocked)

  apply (rule_tac B="\<lambda>rv s. iscc_valid_sched_predicate sc_ptr tcb_ptr mrefills budget s
                            \<and> budget \<le> period \<and> period \<le> MAX_SC_PERIOD \<and> current_time_bounded 2 s
                            \<and> ex_nonz_cap_to sc_ptr s \<and> consumed_time_bounded s
                            \<and> sc_refill_max_sc_at (\<lambda>rm. rm = sc_refill_max sc) sc_ptr s
                            \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s
                            \<and> not_in_release_q tcb_ptr s \<and> cur_sc_offset_ready (consumed_time s) s
                            \<and> cur_sc_in_release_q_imp_zero_consumed s \<and> cur_sc_active s
                            \<and> not_queued tcb_ptr s "
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: tcb_sched_dequeue_valid_sched_except_blocked
                     tcb_sched_dequeue_valid_blocked_except_set
                     tcb_release_remove_ready_or_release tcb_sched_dequeue_ct_not_queued)
    apply (rule tcb_dequeue_not_queued)
   apply clarsimp
   apply (intro conjI)
    apply (clarsimp simp: valid_sched_def split: if_splits)
    using valid_blocked_except_set_in_ready_q apply blast
   apply (clarsimp simp: valid_sched_def)

  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rename_tac csc)
  apply (rule_tac B="\<lambda>rv s. iscc_valid_sched_predicate sc_ptr tcb_ptr mrefills budget s
                            \<and> budget \<le> period \<and> period \<le> MAX_SC_PERIOD \<and> current_time_bounded 2 s
                            \<and> sc_tcb_sc_at (\<lambda>tcb. tcb = sc_tcb sc) sc_ptr s
                            \<and> sc_refill_max_sc_at (\<lambda>rm. rm = sc_refill_max sc) sc_ptr s
                            \<and> not_in_release_q tcb_ptr s \<and> consumed_time_bounded s
                            \<and> cur_sc_active s
                            \<and> not_queued tcb_ptr s"
           in hoare_seq_ext[rotated])

   apply (case_tac "sc_ptr \<noteq> csc")
    apply (wpsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)

   \<comment> \<open>sc_ptr = csc\<close>
   apply (clarsimp simp: valid_sched_def)
   apply (wpsimp wp: commit_time_valid_release_q_cur_sc_not_in_release_q commit_time_invs
                     commit_time_valid_ready_qs commit_time_valid_sched_action
                     commit_time_released_ipc_queues commit_time_valid_blocked_except_set
                     commit_time_sc_refill_max_sc_at
                     commit_time_active_sc_valid_refills)
   apply (simp add: sc_at_pred_n_def obj_at_def)
   apply (intro conjI impI)
        apply (clarsimp simp: vs_all_heap_simps obj_at_def)
        apply (frule invs_sym_refs)
        apply (frule sym_ref_tcb_sc; blast?)
        apply simp
       apply (clarsimp simp: vs_all_heap_simps obj_at_def)
       apply (frule invs_sym_refs)
       apply (frule sym_ref_tcb_sc; blast?)
       apply simp
      apply (erule schact_is_rct_simple)

  apply (rule_tac B="\<lambda>rv s. valid_sched_except_blocked s
                            \<and> budget \<le> period \<and> period \<le> MAX_SC_PERIOD \<and> current_time_bounded 2 s
                            \<and> valid_blocked_except tcb_ptr s \<and> consumed_time_bounded s
                            \<and> invs s
                            \<and> pred_map_eq (Some sc_ptr) (tcb_scps_of s) tcb_ptr
                            \<and> sc_tcb_sc_at (\<lambda>tcb. tcb = sc_tcb sc) sc_ptr s
                            \<and> active_sc_tcb_at tcb_ptr s
                            \<and> sc_ptr \<noteq> idle_sc_ptr"
           in hoare_seq_ext)

   apply (rule hoare_seq_ext[OF _ gts_sp])
   apply (rename_tac thread_state2)
   apply (simp only: valid_sched_def cong: conj_cong)
   apply (rule_tac B="\<lambda>rv s. valid_sched_except_blocked s
                             \<and> budget \<le> period \<and> period \<le> MAX_SC_PERIOD \<and> current_time_bounded 2 s
                             \<and> valid_blocked_except tcb_ptr s
                             \<and> invs s \<and> consumed_time_bounded s
                             \<and> (runnable thread_state2
                                \<longrightarrow> not_in_release_q tcb_ptr s \<longrightarrow> released_sc_tcb_at tcb_ptr s)
                             \<and> pred_map_eq (thread_state2) (tcb_sts_of s) tcb_ptr
                             \<and> sc_tcb_sc_at (\<lambda>tcb. tcb = sc_tcb sc) sc_ptr s
                             \<and> sc_ptr \<noteq> idle_sc_ptr"
           in hoare_seq_ext[rotated])
    apply (simp only: valid_sched_def cong: conj_cong)
    apply (wpsimp wp: sched_context_resume_valid_ready_qs sched_context_resume_valid_release_q
                      sched_context_resume_valid_sched_action_with_sym_refs
                      sched_context_resume_valid_blocked_except_set
                      sched_context_resume_sc_tcb_sc_at
                      hoare_vcg_const_imp_lift sched_context_resume_cond_released_sc_tcb_at')
    apply (intro conjI impI)
        apply (erule invs_sym_refs)
       apply (clarsimp simp: pred_map_eq_def pred_map_def obj_at_kh_kheap_simps)
      apply (fastforce simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (clarsimp simp: pred_map_eq_def pred_map_def obj_at_kh_kheap_simps)

   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp split: if_split)
   apply (intro conjI impI)
    apply (rule hoare_weaken_pre[where Q=valid_sched])
     apply (simp add: valid_sched_def)
     apply (wpsimp wp: reschedule_valid_sched_const[simplified valid_sched_def, simplified])
    using valid_blocked_except_cur_thread valid_sched_def apply force
   apply (simp add: valid_sched_def)
   apply (wpsimp wp: possible_switch_to_valid_sched_weak[simplified valid_sched_def, simplified])
   apply (clarsimp split: if_split)
   apply (intro conjI impI)
     apply (erule (1) pred_map_eq_pred_mapE)
    apply (frule invs_valid_idle)
    apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def vs_all_heap_simps)
   apply (clarsimp simp: vs_all_heap_simps runnable_eq_active elim!: valid_blockedE')

  apply (clarsimp split: if_split)
  apply (intro conjI impI)
   apply (rule hoare_seq_ext[OF _ gts_sp])
   apply (rename_tac thread_state)
   apply (clarsimp simp: valid_sched_def split: if_split)
   apply (intro conjI impI)

     \<comment> \<open>refill_update branch\<close>
    apply (wpsimp wp: refill_update_valid_ready_qs refill_update_valid_release_q
                      refill_update_valid_sched_action refill_update_released_ipc_queues
                      refill_update_invs refill_update_valid_blocked_except_set
                      refill_update_sc_tcb_sc_at refill_update_active_sc_tcb_at
                      refill_update_released_sc_tcb_at_indep
                      refill_update_active_sc_valid_refills)
    apply (simp add: active_sc_valid_refills_def obj_at_kh_kheap_simps pred_map_eq_normalise schact_is_rct_simple)
    apply (frule (1) heap_refs_retractD[OF invs_retract_sc_tcbs])
    apply (clarsimp simp: heap_refs_inj_prop[OF invs_inj_tcb_scps] runnable_eq)
    apply (clarsimp simp: active_sc_def MIN_REFILLS_def vs_all_heap_simps)
    apply (elim disjE; simp)

   \<comment> \<open>the remaining subgoals are handled very similarly, and have almost exactly the same proof\<close>
   apply (wpsimp wp: refill_new_valid_ready_qs refill_new_valid_release_q refill_new_invs
                     refill_new_valid_sched_action refill_new_schedulable_ipc_queues
                     refill_new_valid_blocked_except_set refill_new_active_sc_tcb_at
                     refill_new_released_sc_tcb_at refill_new_active_sc_valid_refills)
   apply (simp add: active_sc_valid_refills_def obj_at_kh_kheap_simps pred_map_eq_normalise schact_is_rct_simple)
   apply (frule (1) heap_refs_retractD[OF invs_retract_sc_tcbs])
   apply (clarsimp simp: heap_refs_inj_prop[OF invs_inj_tcb_scps]
                         runnable_eq MIN_REFILLS_def active_sc_def
                         order_trans[OF MIN_BUDGET_le_MIN_SC_BUDGET]
                         current_time_bounded1_drop_WCET[OF current_time_bounded_strengthen])
   apply (clarsimp simp: vs_all_heap_simps)

  apply (clarsimp simp: valid_sched_def)
  apply (wpsimp wp: refill_new_valid_ready_qs refill_new_valid_release_q refill_new_invs
                    refill_new_valid_sched_action refill_new_schedulable_ipc_queues
                    refill_new_valid_blocked_except_set refill_new_active_sc_tcb_at
                    refill_new_released_sc_tcb_at refill_new_active_sc_valid_refills)
  apply (simp add: active_sc_valid_refills_def obj_at_kh_kheap_simps pred_map_eq_normalise schact_is_rct_simple)
  apply (frule (1) heap_refs_retractD[OF invs_retract_sc_tcbs])
  apply (clarsimp simp: heap_refs_inj_prop[OF invs_inj_tcb_scps]
                        runnable_eq MIN_REFILLS_def active_sc_def
                        order_trans[OF MIN_BUDGET_le_MIN_SC_BUDGET]
                        current_time_bounded1_drop_WCET[OF current_time_bounded_strengthen])
  apply (clarsimp simp: vs_all_heap_simps)
  done

end

lemma ct_active_imp_not_timeout:
  "\<lbrakk>invs s; ct_active s\<rbrakk> \<Longrightarrow> \<not> timeout_faulted_tcb_at (cur_thread s) s"
  by (fastforce dest!: invs_fault_tcbs_valid_states fault_tcbs_valid_states_active
                simp: ct_in_state_def tcb_at_kh_simps is_timeout_fault_opt_def pred_map_def)

context DetSchedSchedule_AI_det_ext begin

lemma perform_invocation_valid_sched:
  "\<lbrace>invs and valid_invocation i and ct_active and scheduler_act_sane and valid_sched
        and ready_or_release and valid_reply_scs and cur_sc_active
        and schact_is_rct and ct_not_queued and ct_not_in_release_q and ct_released
        and current_time_bounded 2 and consumed_time_bounded
        and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   perform_invocation block call can_donate i
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases i; simp)
             apply (wpsimp wp: invoke_untyped_valid_sched)
            apply (wpsimp wp: send_ipc_valid_sched)
            apply (clarsimp simp: valid_sched_valid_sched_except_blocked valid_blockedD
                                  valid_idle_idle_thread_is_idle[OF invs_valid_idle]
                                  ct_active_imp_not_timeout)
            apply (clarsimp simp: vs_all_heap_simps)
           apply (wpsimp wp: send_signal_valid_sched)
           apply (fastforce elim!: ct_in_state_weaken current_time_bounded_strengthen)
          apply (wpsimp wp: do_reply_transfer_valid_sched)
          apply (fastforce elim: current_time_bounded_strengthen)
         apply (wpsimp wp: invoke_tcb_valid_sched)
         apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)
        apply (wpsimp wp: invoke_domain_valid_sched)
        apply (clarsimp simp: vs_all_heap_simps schact_is_rct_def)
       apply (wpsimp wp: invoke_sched_context_valid_sched;
              clarsimp simp: tcb_at_kh_simps vs_all_heap_simps schact_is_rct_def
                      elim!: current_time_bounded_strengthen)
      apply (wpsimp wp: invoke_sched_control_configure_valid_sched)
     apply (wpsimp wp: invoke_cnode_valid_sched)
    apply (wpsimp wp: invoke_irq_control_valid_sched invoke_irq_handler_valid_sched;
           clarsimp simp: invs_valid_objs invs_valid_idle)
   apply (wpsimp wp: arch_perform_invocation_valid_sched;
          intro conjI; clarsimp)
  apply wpsimp
  done

end

lemma set_thread_state_valid_reply_scs[wp]:
  "\<lbrace>valid_reply_scs\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_reply_scs\<rbrace>"
  by (wpsimp wp: valid_reply_scs_lift)

context DetSchedSchedule_AI_det_ext begin

lemma lookup_extra_caps_not_timeout[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps thread buffer mi -, \<lbrace>\<lambda>rv s. \<not> is_timeout_fault rv\<rbrace>"
  apply (simp add: lookup_extra_caps_def split del: if_split)
  by (wpsimp wp: mapME_wp' lookup_cap_and_slot_valid_fault)

lemma handle_invocation_valid_sched:
  "\<lbrace>invs
    and valid_sched
    and ready_or_release
    and ct_active
    and ct_not_queued
    and ct_not_in_release_q
    and valid_reply_scs
    and cur_sc_active
    and schact_is_rct
    and ct_released
    and current_time_bounded 2
    and consumed_time_bounded
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
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
                 sts_schedulable_scheduler_action
            hoare_vcg_E_conj | simp add: split_def if_apply_def2 split del: if_split)+
  apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_ready_qs_def not_queued_def
                    is_schedulable_bool_def2 ct_in_state_def runnable_eq_active not_in_release_q_def
                    in_release_queue_def released_sc_tcb_at_def)
  apply (auto elim: st_tcb_ex_cap st_tcb_at_strengthen_pred intro: fault_tcbs_valid_states_active)
  done

end

lemma valid_sched_ct_not_queued:
  "\<lbrakk>valid_sched s; scheduler_action s = resume_cur_thread\<rbrakk> \<Longrightarrow>
    not_queued (cur_thread s) s"
  by (fastforce simp: valid_sched_def ct_not_in_q_def)


context DetSchedSchedule_AI begin

crunch cur[wp]: handle_fault_reply "cur_tcb :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

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
     do_reply_transfer sender receiver grant
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc |
         clarsimp split del: if_split | wp_once hoare_drop_imps)+
  *)

(*
lemma do_reply_transfer_schedact_not:
  "\<lbrace>scheduler_act_not t and K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver grant
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc | clarsimp split del: if_split |
         wp_once hoare_drop_imps)+
  *)

(*
lemma do_reply_transfer_add_assert:
  assumes a: "\<lbrace>(\<lambda>s. reply_tcb_reply_at (\<lambda>p. p = Some receiver \<longrightarrow>
                                       st_tcb_at awaiting_reply receiver s) rptr s) and P\<rbrace>
               do_reply_transfer sender rptr grant
              \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> do_reply_transfer sender rptr grant \<lbrace>\<lambda>_. Q\<rbrace>"
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

(*
lemma do_reply_transfer_ct_not_queued:
  "\<lbrace>ct_not_queued and invs and ct_active and scheduler_act_sane\<rbrace>
     do_reply_transfer sender receiver grant
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

end

locale DetSchedSchedule_AI_handle_hypervisor_fault =
  DetSchedSchedule_AI state_ext_t for state_ext_t :: "'state_ext::state_ext itself" +
  assumes handle_hyp_fault_valid_sched[wp]:
    "\<And>t fault.
      \<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
          and ct_in_state activatable\<rbrace>
        handle_hypervisor_fault t fault
      \<lbrace>\<lambda>_. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  (* commented predicate apparently not needed in ARM_HYP case. This is not verified and
     assumed for the ARM case. *)
  assumes handle_reserved_irq_valid_sched' [wp]:
    "\<And>irq.
      \<lbrace>valid_sched and invs and
         (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<comment>\<open>\<and> ct_not_queued s\<close> )\<rbrace>
        handle_reserved_irq irq
      \<lbrace>\<lambda>rv. valid_sched :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes handle_hyp_fault_cur_time[wp]:
    "\<And>t fault P. handle_hypervisor_fault t fault
                \<lbrace>(\<lambda>s. P (consumed_time s) (cur_sc s) (cur_time s) (cur_domain s)
                        (cur_thread s) (idle_thread s) (last_machine_time_of s)
                        (sc_refill_cfgs_of s) (etcbs_of s)) :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes handle_hypervisor_fault_scheduler_act_sane[wp]:
    "\<And>t fault.
     \<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
     handle_hypervisor_fault t fault
     \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes handle_reserved_irq_scheduler_act_sane[wp]:
    "\<And>irq. handle_reserved_irq irq \<lbrace>scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_not_timeout_fault[wp]:
    "\<And>thread ft.
      \<lbrace>\<top>::'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault thread ft -,\<lbrace>\<lambda>rv s.  \<not> is_timeout_fault rv\<rbrace>"

locale DetSchedSchedule_AI_handle_hypervisor_fault_det_ext =
  DetSchedSchedule_AI_handle_hypervisor_fault "TYPE (det_ext)"
  + DetSchedSchedule_AI_det_ext

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_interrupt_valid_sched:
  "\<lbrace>valid_sched
    and invs
    and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s)
    and current_time_bounded 1 \<rbrace>
  handle_interrupt irq \<lbrace>\<lambda>rv. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  apply (wpsimp wp: get_cap_wp hoare_drop_imps hoare_vcg_all_lift send_signal_valid_sched
              simp: do_machine_op_bind current_time_bounded_def)
  done

crunch not_ct[wp]: handle_fault,lookup_reply,lookup_cap,receive_ipc,receive_signal
  "not_cur_thread target::'state_ext state \<Rightarrow> _"
  (wp: mapM_wp' maybeM_inv hoare_drop_imp hoare_vcg_if_lift2 simp: unless_def)

lemma handle_recv_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread target\<rbrace> handle_recv param_a param_b \<lbrace>\<lambda>_. not_cur_thread target::'state_ext state \<Rightarrow> _\<rbrace>"
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
  apply (clarsimp simp: refill_budget_check_def)
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

lemma postpone_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> postpone scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: postpone_def)
  apply (wpsimp simp: tcb_sched_action_def get_sc_obj_ref_def thread_get_def
                  wp: get_sched_context_wp hoare_drop_imp
                      set_tcb_queue_wp)
  by (clarsimp simp: in_queues_2_def tcb_sched_ready_q_update_set_simps split: option.splits)

crunches set_extra_badge
  for ct_active[wp]: "ct_active::'state_ext state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps dxo_wp_weak simp: cap_insert_ext_def)

lemma set_message_info_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_. ct_active\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def ct_in_state_def split_def set_object_def)

crunches do_normal_transfer, do_fault_transfer
  for ct_active[wp]: "ct_active::'state_ext state \<Rightarrow> _"
  (simp: zipWithM_x_mapM wp: mapM_wp' transfer_caps_loop_pres)


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
    apply (wpsimp wp: set_thread_state_Inactive_simple_sched_action_not_runnable)
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
  apply (auto simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def is_sc_active_def
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

end

lemma next_domain_valid_list[wp]:
  "next_domain \<lbrace>valid_list\<rbrace>"
  unfolding next_domain_def Let_def
  apply (fold reset_work_units_def)
  apply (wpsimp | simp add: reset_work_units_def)+
  done

crunch valid_list[wp]: switch_sched_context,set_next_interrupt valid_list (wp: hoare_drop_imp)

lemma sc_and_timer_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> sc_and_timer \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by (wpsimp simp: sc_and_timer_def)

context DetSchedSchedule_AI begin

lemma reply_push_cannot_donate_active_sc_tcb_at[wp]:
  "reply_push caller callee reply_ptr False
   \<lbrace>\<lambda>(s:: 'state_ext state). active_sc_tcb_at t s\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: hoare_drop_imp)

lemma send_ipc_cannot_donate_active_sc_tcb_at[wp]:
  "send_ipc block call badge can_grant can_grant_reply False thread epptr
   \<lbrace>\<lambda>(s:: 'state_ext state). active_sc_tcb_at t s\<rbrace>"
  unfolding send_ipc_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)

lemma end_timeslice_canTimeout_active_sc_tcb_at[wp]:
  "end_timeslice True
   \<lbrace>\<lambda>(s:: 'state_ext state). active_sc_tcb_at t s\<rbrace>"
  unfolding end_timeslice_def handle_timeout_def send_fault_ipc_def
  by (wpsimp wp: hoare_drop_imp)

lemma check_budget_canTimeout_active_sc_tcb_at[wp]:
  "charge_budget consumeda True
   \<lbrace>\<lambda>(s:: 'state_ext state). active_sc_tcb_at t s\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp)

lemma check_budget_ct_active_sc_tcb_at[wp]:
  "check_budget
   \<lbrace>\<lambda>(s:: 'state_ext state). active_sc_tcb_at (cur_thread s) s\<rbrace>"
  unfolding check_budget_def
  apply wpsimp
  apply (rule_tac Q="\<lambda>r s. \<forall>t. t = cur_thread s \<longrightarrow> active_sc_tcb_at t s" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply simp+
  by (wpsimp wp: hoare_drop_imp)+

lemma invs_strengthen_cur_sc_tcb_are_bound:
  "schact_is_rct s \<and> invs s \<Longrightarrow> cur_sc_tcb_are_bound s"
  by (fastforce simp: tcb_at_kh_simps[symmetric]
               intro: cur_sc_tcb_rev)

lemma check_budget_restart_valid_sched:
  "\<lbrace>valid_sched
    and invs
    and ct_not_in_release_q
    and ct_not_queued
    and schact_is_rct
    and ct_released
    and current_time_bounded 2
    and consumed_time_bounded
    and cur_sc_active
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
    and cur_sc_not_blocked\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>rv s::'state_ext state. \<not>rv \<longrightarrow> valid_sched s\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (wpsimp wp: gts_wp hoare_vcg_all_lift set_thread_state_Restart_valid_sched)
   apply (rule_tac Q="\<lambda>r s. valid_sched s \<and> (\<not>r \<longrightarrow> active_sc_tcb_at (cur_thread s) s)" in hoare_strengthen_post[rotated])
    apply (clarsimp simp: ct_in_state_def runnable_eq_active tcb_at_kh_simps vs_all_heap_simps)
   apply (wpsimp wp: hoare_vcg_if_lift2 check_budget_valid_sched hoare_drop_imp)
  apply (simp add: invs_retract_tcb_scps[THEN heap_refs_retract_heap_refs_retract_at])
  apply (intro conjI)
    apply clarsimp
   apply (fastforce intro: invs_cur_sc_chargeableE)
  apply (fastforce simp: vs_all_heap_simps)
  done

lemma handle_yield_valid_sched:
  "\<lbrace>valid_sched
    and invs
    and ct_not_in_release_q
    and ct_not_queued
    and ct_not_blocked
    and schact_is_rct
    and cur_sc_chargeable
    and current_time_bounded 2
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
    and cur_sc_active\<rbrace>
   handle_yield
   \<lbrace>\<lambda>rv. valid_sched::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_yield_def
  apply (wpsimp wp: charge_budget_valid_sched get_refills_wp
              simp: invs_retract_tcb_scps[THEN heap_refs_retract_heap_refs_retract_at])
  apply (intro conjI)
     apply (clarsimp)
    apply (drule ct_not_blocked_cur_sc_not_blocked; simp)
   apply (rule_tac y=" unat MAX_SC_PERIOD + unat MAX_SC_PERIOD" in order_trans[rotated])
    apply (clarsimp simp: current_time_bounded_def)
   apply (rule add_mono[rotated], simp)
   apply (clarsimp simp: valid_sched_def active_sc_valid_refills_def)
   apply (drule_tac x="cur_sc s" in spec, clarsimp)
   apply (clarsimp simp: unat_le_mono[symmetric])
   apply (rule valid_refills_r_amount_bounded_max_sc_period)
   apply (clarsimp simp: valid_refills_def2 obj_at_def)
  apply (clarsimp simp: cur_sc_offset_ready_def obj_at_def refill_ready_def)
  apply (simp add: unat_le_mono)
  apply (subst (asm) unat_add_lem', overflow_hammer)
   apply (clarsimp simp: current_time_bounded_def)
  apply (clarsimp simp: vs_all_heap_simps)
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

lemma update_time_stamp_ct_budget_ready[wp]:
 "\<lbrace>(\<lambda>s. budget_ready (cur_thread s) s) and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_ s. budget_ready (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>t. t = cur_thread s \<and> budget_ready t s"
   in hoare_strengthen_post)
  by (wpsimp wp: hoare_vcg_ex_lift)+

lemma update_time_stamp_ct_budget_sufficient[wp]:
 "\<lbrace>(\<lambda>s. budget_sufficient (cur_thread s) s) and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_ s. budget_sufficient (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>t. t = cur_thread s \<and> budget_sufficient t s"
   in hoare_strengthen_post)
  by (wpsimp wp: hoare_vcg_ex_lift)+

lemma update_time_stamp_ct_released[wp]:
 "\<lbrace>ct_released and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_. ct_released\<rbrace>"
  by (wpsimp simp: released_sc_tcb_at_def)

lemma update_time_stamp_released_if_bound_sc_tcb_at[wp]:
 "\<lbrace>\<lambda>s :: 'state_ext state. released_if_bound_sc_tcb_at (cur_thread s) s \<and> valid_machine_time s\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_ s. released_if_bound_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp wp: hoare_vcg_disj_lift simp: released_sc_tcb_at_def)

lemma update_time_stamp_ct_active_sc_tcb_at[wp]:
 "\<lbrace>(\<lambda>s. active_sc_tcb_at (cur_thread s) s) and valid_machine_time :: 'state_ext state \<Rightarrow> _\<rbrace>
  update_time_stamp
  \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. \<exists>t. t = cur_thread s \<and> active_sc_tcb_at t s"
   in hoare_strengthen_post)
  by (wpsimp wp: hoare_vcg_ex_lift)+

(* FIXME maybe move *)
lemma wcet_offset_translate:
  "x \<le> - kernelWCET_ticks - 1 \<Longrightarrow> unat x + unat kernelWCET_ticks < 2^ len_of TYPE (64)"
  by (force dest: word_leq_minus_one_le[rotated] no_plus_overflow_neg simp: no_olen_add_nat kernelWCET_ticks_non_zero)

crunches do_machine_op
  for valid_reply_scs[wp]: valid_reply_scs
  (wp:  crunch_wps dmo_getCurrentTime_sp simp: crunch_simps)

lemma update_time_stamp_ready_or_release[wp]:
  "\<lbrace>valid_machine_time and ready_or_release::'state_ext state \<Rightarrow> _\<rbrace> update_time_stamp \<lbrace>\<lambda>_. ready_or_release\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="valid_machine_time and (ready_or_release and (\<lambda>s. cur_time s = prev_time))"
                in hoare_weaken_pre[rotated]; clarsimp)
  apply (rule hoare_seq_ext[OF _ dmo_getCurrentTime_sp])
  by wpsimp+

lemma update_time_stamp_valid_reply_scs[wp]:
  "\<lbrace>valid_machine_time and valid_reply_scs::'state_ext state \<Rightarrow> _\<rbrace>update_time_stamp \<lbrace>\<lambda>_. valid_reply_scs\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="valid_machine_time and (valid_reply_scs and (\<lambda>s. cur_time s = prev_time))"
                in hoare_weaken_pre[rotated]; clarsimp)
  apply (rule hoare_seq_ext[OF _ dmo_getCurrentTime_sp])
   apply wpsimp
  by (clarsimp simp: valid_reply_scs_def split: option.splits) wpsimp

lemma update_time_stamp_cur_sc_offset_ready[wp]:
  "\<lbrace>valid_machine_time and cur_sc_offset_ready used::'state_ext state \<Rightarrow> _\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. cur_sc_offset_ready used\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac Q="valid_machine_time and (cur_sc_offset_ready used and (\<lambda>s. cur_time s = prev_time))"
                in hoare_weaken_pre[rotated]; clarsimp)
  apply (rule hoare_seq_ext[OF _ dmo_getCurrentTime_sp])
   apply wpsimp
   apply (clarsimp simp: cur_sc_offset_ready_def vs_all_heap_simps unat_arith_simps(1) split: option.splits)
  by wpsimp

lemma valid_refills_cur_time[simp]:
  "valid_refills sc (s\<lparr>cur_time := b\<rparr>) = valid_refills sc s"
  by (clarsimp simp: valid_refills_def)

lemma valid_sched_valid_machine_time[elim!]:
  "valid_sched s \<Longrightarrow> valid_machine_time s"
  by (simp add: valid_sched_def)

crunches handle_fault, reply_from_kernel
  for ct_not_in_release_q[wp]: "ct_not_in_release_q::'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunches invoke_domain, handle_timeout
  for ct_not_in_release_q[wp]: "ct_not_in_release_q::'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

lemma charge_budget_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane::'state_ext state \<Rightarrow> _\<rbrace>
   charge_budget consumed can_timeout
   \<lbrace>\<lambda>_. scheduler_act_sane ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: is_schedulable_wp hoare_drop_imp)

lemma check_budget_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane::'state_ext state \<Rightarrow> _\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. scheduler_act_sane ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: is_schedulable_wp hoare_drop_imp)

lemma send_ipc_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate thread epptr
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: send_ipc_def wp: hoare_drop_imp possible_switch_to_scheduler_act_sane' gts_wp)
  apply (rule_tac Q="\<lambda>_. scheduler_act_sane and ct_not_blocked" in hoare_strengthen_post[rotated])
  apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps vs_all_heap_simps, fastforce)
  apply (wpsimp simp: send_ipc_def wp: hoare_drop_imp hoare_vcg_all_lift)+
  done

lemma maybe_donate_sc_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane \<rbrace>
   maybe_donate_sc a g
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
   unfolding maybe_donate_sc_def
   by (wpsimp wp: hoare_drop_imp)

lemma update_waiting_ntfn_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and (\<lambda>s. queue \<noteq> [] \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace>
   update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace>\<lambda>_. scheduler_act_sane ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding update_waiting_ntfn_def
  by (wpsimp wp: possible_switch_to_scheduler_act_sane' is_schedulable_wp
                 hoare_drop_imp)+

lemma send_signal_scheduler_act_sane:
  "\<lbrace>scheduler_act_sane
    and ct_not_BlockedOnNtfn
    and ct_in_state not_BlockedOnReceive
    and invs\<rbrace>
   send_signal ntfnptr badge
   \<lbrace>\<lambda>_. scheduler_act_sane ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_signal_def
  apply (wpsimp wp: possible_switch_to_scheduler_act_sane' is_schedulable_wp)+
           apply (wpsimp wp: hoare_drop_imps)
          apply (wpsimp wp: gts_wp get_simple_ko_wp)+
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps receive_blocked_def vs_all_heap_simps is_BlockedOnReceive_def)
   apply (case_tac "tcb_state y"; simp)
  apply (prop_tac "tcb_at (hd x) s")
   apply (clarsimp)
  apply (prop_tac "(hd x, NTFNSignal) \<in> state_refs_of s ntfnptr")
   apply (clarsimp simp: state_refs_of_def refs_of_def get_refs_def obj_at_def split: option.splits)
  using hd_in_set apply fastforce
  apply (drule sym_refsD, clarsimp)
  apply (clarsimp)
  apply (drule TCBSignal_in_state_refs_of)
  by (clarsimp simp: tcb_at_kh_simps ct_in_state_def pred_map_eq_normalise vs_all_heap_simps)

lemma do_reply_transfer_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   do_reply_transfer sender reply grant
   \<lbrace>\<lambda>_. scheduler_act_sane ::'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding do_reply_transfer_def handle_timeout_def
  apply (wpsimp wp: possible_switch_to_scheduler_act_sane' thread_set_ct_in_state simp: send_fault_ipc_def)
              apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp hoare_vcg_if_lift2 sts_ctis_neq thread_set_ct_in_state)+
                apply (rule_tac Q="\<lambda>_ s. scheduler_act_sane s \<and> x \<noteq> cur_thread s \<and> ct_not_blocked s" in hoare_strengthen_post[rotated])
                 apply (clarsimp)
                apply ((wpsimp wp: hoare_drop_imp)+)[12]
    apply (wpsimp wp: gts_wp get_simple_ko_wp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_eq_commute)
  by (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)

lemma invoke_domain_valid_sched_misc[wp]:
  "invoke_domain thread domain
   \<lbrace>\<lambda>s. P (consumed_time s) (cur_sc s) (ep_send_qs_of s) (ep_recv_qs_of s) (cur_time s)
          (cur_domain s) (cur_thread s) (idle_thread s) (release_queue s) (last_machine_time_of s)
          (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp simp: set_domain_def)

lemma invoke_domain_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   invoke_domain thread domain
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  unfolding invoke_domain_def
  by (wpsimp simp: set_domain_def wp: hoare_vcg_if_lift2)

lemma sched_context_bind_ntfn_valid_sched_pred_strong[wp]:
  "sched_context_bind_ntfn sc ntfn \<lbrace>valid_sched_pred_strong P\<rbrace>"
  unfolding sched_context_bind_ntfn_def
  by wpsimp

lemma sched_context_yield_to_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane
    and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) scptr s)\<rbrace>
   sched_context_yield_to scptr args
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: sched_context_yield_to_def assert_opt_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (clarsimp simp: when_def complete_yield_to_def bind_assoc maybeM_def get_tcb_obj_ref_def
                         get_sc_obj_ref_def)
   apply (rule hoare_seq_ext_skip, wpsimp, rename_tac yield_tcb)
   apply (case_tac yield_tcb; clarsimp)
    apply (wpsimp wp: hoare_drop_imps)
   apply (clarsimp simp: bind_assoc assert_opt_def)
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext_skip)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift'
                simp: set_consumed_def)
   apply (wpsimp wp: set_object_wp update_sched_context_wp
               simp: set_tcb_obj_ref_def)
   apply (fastforce simp: sc_at_pred_n_def get_tcb_def obj_at_def split: if_splits)
  apply (rule hoare_seq_ext[OF _ gsct_sp], rename_tac sc_tcb_opt)
  apply (case_tac sc_tcb_opt; clarsimp?)
  apply (rule hoare_seq_ext_skip)
   apply ((wpsimp wp:sched_context_resume_sc_tcb_sc_at | wps)+)[1]
  by (wpsimp wp: set_scheduler_action_wp hoare_vcg_all_lift hoare_drop_imps
           simp: sc_at_pred_n_def obj_at_def scheduler_act_not_def
          split: if_splits
      | wps)+

lemma invoke_sched_context_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and valid_sched_context_inv iv\<rbrace>
   invoke_sched_context iv
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding invoke_sched_context_def
  apply (case_tac iv; simp)
  by (wpsimp simp:  wp: hoare_vcg_if_lift2)+

lemma invoke_sched_control_configure_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   invoke_sched_control_configure x8
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding invoke_sched_control_configure_def
  apply wpsimp
               apply (wpsimp wp: possible_switch_to_scheduler_act_sane' )
              apply (wpsimp wp:  hoare_vcg_if_lift2 hoare_vcg_imp_lift' )
             apply (wpsimp wp:  hoare_vcg_if_lift2 hoare_vcg_imp_lift' )
            apply (rule_tac Q="\<lambda>_ s. scheduler_act_sane s" in hoare_strengthen_post[rotated])
             apply (clarsimp split: if_split)
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+

crunches invoke_irq_control
  for scheduler_act_sane[wp]: "scheduler_act_sane::'state_ext state \<Rightarrow> _"

crunches invoke_irq_handler
  for scheduler_act_sane[wp]: "scheduler_act_sane::'state_ext state \<Rightarrow> _"

(* FIXME: RT move *)
lemma ct_activatable_ct_not_blocked[elim!]:
  "ct_in_state activatable s \<Longrightarrow> ct_not_blocked s"
  apply (erule ct_in_state_weaken)
  apply (fastforce dest: ipc_queued_thread_state_not_runnable)
  done

(* FIXME: RT move *)
lemma ct_activatable_ct_not_BlockedOnNtfn[elim!]:
  "ct_in_state activatable s \<Longrightarrow> ct_not_BlockedOnNtfn s"
  apply (erule ct_in_state_weaken)
  apply (case_tac st; simp)
  done

(* FIXME: RT move *)
lemma ct_activatable_ct_not_BlockedOnReceive[elim!]:
  "ct_in_state activatable s \<Longrightarrow> ct_in_state not_BlockedOnReceive s"
  apply (erule ct_in_state_weaken)
  apply (case_tac st; simp add: is_BlockedOnReceive_def)
  done

lemma perform_invocation_scheduler_act_sane[wp]:
  "\<lbrace>valid_invocation iv and simple_sched_action and ct_in_state activatable and invs\<rbrace>
   perform_invocation block call can_donate iv
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
  by (wpsimp wp: hoare_drop_imp invoke_cnode_scheduler_act_sane send_signal_scheduler_act_sane
                 invoke_tcb_scheduler_act_sane | fastforce)+

lemma postpone_ct_not_in_release_q:
  "\<lbrace>ct_not_in_release_q and (\<lambda>s. \<forall>t. sc_tcb_sc_at ((=) (Some t)) scp s \<longrightarrow> t\<noteq>cur_thread s)\<rbrace>
   postpone scp
   \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: tcb_release_enqueue_ct_not_in_release_q get_sc_obj_ref_wp)
  by (fastforce simp: sc_at_pred_n_def obj_at_def)

lemma postpone_ct_not_queued:
  "\<lbrace>ct_not_queued and (\<lambda>s. \<not> heap_ref_eq (cur_thread s) sc_ptr (sc_tcbs_of s))\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (simp add: postpone_def)
  by (wpsimp wp: get_sc_obj_ref_wp tcb_dequeue_not_queued_gen | wps)+

lemma postpone_not_queued_other:
  "\<lbrace>not_queued t and (\<lambda>s. \<not> heap_ref_eq t sc_ptr (sc_tcbs_of s))\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: postpone_def)
  by (wpsimp wp: tcb_release_enqueue_not_in_release_q get_sc_obj_ref_wp tcb_dequeue_not_queued_gen)

lemma sched_context_resume_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> \<not> heap_ref_eq (cur_thread s) sc_ptr (sc_tcbs_of s)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_ct_not_in_release_q get_tcb_queue_wp is_schedulable_wp
           simp: thread_get_def vs_all_heap_simps obj_at_kh_kheap_simps)

lemma sched_context_resume_not_queued:
  "\<lbrace>not_queued t and (\<lambda>s. \<not> heap_ref_eq t sc_ptr (sc_tcbs_of s))\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: sched_context_resume_def)
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps hoare_vcg_if_lift
                 postpone_not_queued_other
           simp: if_fun_split)

lemma sched_context_resume_ct_not_queued:
  "\<lbrace>\<lambda>s. ct_not_queued s \<and> \<not> heap_ref_eq (cur_thread s) sc_ptr (sc_tcbs_of s)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: get_tcb_queue_wp is_schedulable_wp postpone_not_queued_other
           simp: thread_get_def sc_at_pred_n_def obj_at_def | wps)+

crunches refill_unblock_check
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sched_context_donate_bound_not_cur_thread:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> cur_thread s\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. \<not> heap_ref_eq (cur_thread s) sc_ptr (sc_tcbs_of s)\<rbrace>"
  unfolding sched_context_donate_def
  apply (rule_tac hoare_seq_ext[OF _ gsct_sp])
  apply (rule_tac B = "\<lambda>_ s. tcb_ptr \<noteq> cur_thread s" in hoare_seq_ext)
  apply (wpsimp wp: set_tcb_obj_ref_wp)
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def vs_all_heap_simps obj_at_kh_kheap_simps
                        pred_map_simps)
  by wpsimp

lemma maybe_donate_sc_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and (\<lambda>s. thread \<noteq> cur_thread s):: 'state_ext state \<Rightarrow> _\<rbrace>
   maybe_donate_sc thread scp
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  apply (wpsimp wp: )
        apply (wpsimp wp: sched_context_resume_ct_not_in_release_q hoare_vcg_all_lift hoare_vcg_imp_lift')
       apply (wpsimp wp: sched_context_resume_ct_not_in_release_q hoare_vcg_all_lift hoare_vcg_imp_lift')
      apply simp
      apply (wpsimp wp: sched_context_donate_bound_not_cur_thread
                  simp: vs_all_heap_simps obj_at_kh_kheap_simps)
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  done

lemma update_waiting_ntfn_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and (\<lambda>s. queue \<noteq> [] \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace>
   update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding update_waiting_ntfn_def by wpsimp

lemma send_signal_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and ct_not_blocked and invs\<rbrace>
   send_signal ntfnptr badge
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_signal_def
  apply (wpsimp wp: gts_wp ct_in_state_set hoare_drop_impE get_simple_ko_wp)
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcb"; simp add: receive_blocked_def)
  apply (subgoal_tac "(hd x, NTFNSignal) \<in> state_refs_of s ntfnptr")
  apply (drule sym_refsD; clarsimp)
  apply (drule TCBSignal_in_state_refs_of)
  apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps pred_map_eq_normalise)
  apply (fastforce dest: hd_in_set simp: state_refs_of_def get_refs_def split: option.splits)
  done

lemma sched_context_donate_not_queued[wp]:
  "\<lbrace>ct_not_queued and (\<lambda>s. tcb_ptr \<noteq> cur_thread s) and schact_is_rct\<rbrace>
   sched_context_donate scp tcb_ptr
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp simp: set_tcb_obj_ref_def
               wp: hoare_drop_imp tcb_dequeue_not_queued_gen get_sc_obj_ref_wp | wps)+

lemma maybe_donate_sc_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and (\<lambda>s. tcb_ptr \<noteq> cur_thread s) and schact_is_rct\<rbrace>
   maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  apply (wpsimp wp: sched_context_resume_ct_not_queued)
      apply (wpsimp wp: sched_context_donate_bound_not_cur_thread)
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp)+
  done

lemma test_reschedule_not_ct_schact_is_rct[wp]:
  "\<lbrace>(\<lambda>s. from_tptr \<noteq> cur_thread s) and schact_is_rct\<rbrace>
   test_reschedule from_tptr
   \<lbrace>\<lambda>_. schact_is_rct :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: test_reschedule_def when_def)
  apply (intro hoare_seq_ext[OF _ gets_sp], rename_tac cur action)
  apply (clarsimp, intro conjI impI; (solves \<open>wpsimp\<close>)?)
   apply (clarsimp simp: pred_conj_def)
   apply (metis (mono_tags, lifting) hoare_assume_pre)
  apply (case_tac action; (solves \<open>wpsimp\<close>)?)
  apply (wpsimp simp: schact_is_rct_def)
  apply (metis (mono_tags, lifting) pred_andE pred_conj_assoc scheduler_action.distinct(2)
               valid_pre_satisfies_post)
  done

lemma sched_context_donate_schact_is_rct:
  "\<lbrace>(\<lambda>s. \<not> heap_ref_eq (cur_thread s) sc_ptr (sc_tcbs_of s))
    and schact_is_rct\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. schact_is_rct :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_donate_def when_def
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (clarsimp simp: bind_assoc)
  apply (intro conjI impI; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp simp: sc_at_pred_n_def)
  apply (rule hoare_seq_ext_skip, wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  apply wpsimp
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)
  done

lemma maybe_donate_sc_schact_is_rct[wp]:
  "\<lbrace>(\<lambda>s. tcb_ptr \<noteq> cur_thread s) and schact_is_rct\<rbrace>
   maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>_. schact_is_rct :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def when_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, wpsimp, rename_tac ntfn_sc)
  apply (clarsimp simp: maybeM_def)
  apply (case_tac ntfn_sc; clarsimp?, (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (wpsimp wp: sched_context_donate_schact_is_rct)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)
  done

lemma set_thread_state_act_schact_is_rct:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> cur_thread s \<and> schact_is_rct s\<rbrace>
   set_thread_state_act tcb_ptr
   \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  apply (clarsimp simp: set_thread_state_act_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])+
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_when_cases; fastforce?)
  apply (wpsimp wp: set_scheduler_action_wp)
  done

lemma set_thread_state_act_scheduler_act_sane:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> cur_thread s \<and> scheduler_act_sane s\<rbrace>
   set_thread_state_act tcb_ptr
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: set_thread_state_act_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])+
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_when_cases; fastforce?)
  apply (wpsimp wp: set_scheduler_action_wp)
  done

lemma set_thread_state_schact_is_rct[wp]:
  "\<lbrace>\<lambda>s. ref \<noteq> cur_thread s \<and> schact_is_rct s\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: set_thread_state_act_schact_is_rct)

lemma update_waiting_ntfn_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and (\<lambda>s. queue \<noteq> [] \<longrightarrow> hd queue \<noteq> cur_thread s)
    and schact_is_rct\<rbrace>
   update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding update_waiting_ntfn_def is_schedulable_def when_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
  apply (wpsimp wp: possible_switch_to_ct_not_queued hoare_vcg_all_lift hoare_vcg_conj_lift
              cong: conj_cong)
  done

crunches cancel_ipc
  for schact_is_rct[wp]: "schact_is_rct"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps)

lemma send_signal_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and ct_active and sym_refs \<circ> state_refs_of and schact_is_rct\<rbrace>
   send_signal ntfnptr badge
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding send_signal_def
  apply (clarsimp simp: bind_assoc)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])

  apply (case_tac "ntfn_obj ntfn"; clarsimp?, (solves \<open>wpsimp\<close>)?)
   apply (find_goal \<open>match premises in \<open>_ = WaitingNtfn _ \<close> \<Rightarrow> \<open>-\<close>\<close>)
   apply (rename_tac queue)
   apply wpsimp
   apply (prop_tac "cur_thread s \<in> set queue")
    using list.set_sel(1) apply fastforce
   apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
   apply (frule_tac q=queue and t="cur_thread s" in sym_refs_WaitingNtfn_ipc_queued_thread; blast?)
   apply (metis ipc_queued_thread_state.simps(1) ipc_queued_thread_state.simps(3)
                kernel_object.inject(2) option.inject tcb_sts.all_simps(2))
  apply (case_tac "ntfn_bound_tcb ntfn"; clarsimp?, (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (wpsimp wp: possible_switch_to_not_queued hoare_drop_imp hoare_vcg_all_lift
              simp: is_schedulable_def cong: conj_cong
         | wps)+
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def receive_blocked_def)
  done

lemma do_reply_transfer_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and ct_not_blocked and invs\<rbrace>
   do_reply_transfer sender reply grant
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (case_tac recv_opt, wpsimp, clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac receiver state)
  apply (case_tac "\<forall>r'. state \<noteq> BlockedOnReply r'", solves \<open>wpsimp\<close>, clarsimp)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule_tac S="r'=reply" in hoare_gen_asm''; clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (rule_tac B="\<lambda>_ s. ct_not_in_release_q s \<and> receiver \<noteq> cur_thread s
                            \<and> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_remove_tcb_scps_of_retract)
   apply (clarsimp simp: invs_retract_tcb_scps vs_all_heap_simps ct_in_state_kh_simp)
  apply (rule hoare_seq_ext[OF _ thread_get_inv])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac "runnable state \<longrightarrow> sc_opt = None"
         ; clarsimp simp: pred_conj_def obj_at_kh_kheap_simps pred_map_eq_normalise)
   apply wpsimp
  apply (rename_tac scp)
  apply (rule_tac B="\<lambda>_ s. pred_map_eq (Some scp) (tcb_scps_of s) receiver
                           \<and> pred_map runnable (tcb_sts_of s) receiver
                           \<and> ct_not_in_release_q s \<and> receiver \<noteq> cur_thread s
                            \<and> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: refill_unblock_check_valid_sched_except_blocked hoare_vcg_disj_lift)
   apply (clarsimp simp: pred_map_eq_pred_mapE)
  apply (wpsimp wp: postpone_ct_not_in_release_q)
  apply (frule (1) heap_refs_retractD)
  by (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise vs_all_heap_simps)

lemma handle_timeout_not_queued:
  "\<lbrace>not_queued t and scheduler_act_not t
    and (\<lambda>s. \<forall>qtail tcb. ko_at (TCB tcb) t' s
                         \<longrightarrow> \<not> pred_map_eq (t # qtail) (ep_recv_qs_of s) (cap_ep_ptr (tcb_timeout_handler tcb)))\<rbrace>
   handle_timeout t' ex
   \<lbrace>\<lambda>_. not_queued t :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  apply (wpsimp wp: send_fault_ipc_not_queued_not_ep_queued simp: obj_at_def get_tcb_def)
  apply (case_tac "kheap s t'"; clarsimp?)
  apply (case_tac a; clarsimp?)
  done

lemma handle_timeout_ct_not_queued:
  "\<lbrace>ct_not_queued and scheduler_act_sane
    and (\<lambda>s. \<forall>qtail tcb. ko_at (TCB tcb) t' s
                         \<longrightarrow> \<not> pred_map_eq ((cur_thread s) # qtail) (ep_recv_qs_of s) (cap_ep_ptr (tcb_timeout_handler tcb)))\<rbrace>
   handle_timeout t' ex
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_weaken_pre)
  by (wpsimp wp: handle_timeout_not_queued simp: obj_at_def | wps)+

lemma do_reply_transfer_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and ct_not_blocked and scheduler_act_sane and sym_refs \<circ> state_refs_of
    and tcb_at sender\<rbrace>
   do_reply_transfer sender reply grant
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (clarsimp simp:  do_reply_transfer_def swp_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (case_tac recv_opt; clarsimp?, (solves \<open>wpsimp\<close>)?)
  apply (rename_tac receiver)
  apply (rule hoare_seq_ext[OF _ gts_sp], rename_tac state)
  apply (case_tac state; clarsimp?, (solves \<open>wpsimp\<close>)?)
  apply (rename_tac r)
  apply (case_tac "r = reply"; clarsimp)
  apply (clarsimp simp: sk_obj_at_pred_def obj_at_def)
  apply (rule_tac B="\<lambda>_ s. receiver \<noteq> cur_thread s
                           \<and> ct_not_queued s
                           \<and> (\<forall>ep_ptr q. ep_recv_qs_of s ep_ptr \<noteq> Some (cur_thread s # q))
                           \<and> scheduler_act_sane s
                           \<and> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)
                           \<and> tcb_at receiver s
                           \<and> tcb_at sender s"
            in  hoare_seq_ext[rotated])
   apply (wpsimp wp: reply_remove_tcb_scps_of_retract hoare_vcg_all_lift)
   apply (intro conjI)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def ct_in_state_def)
     apply (case_tac "tcb_state tcb"; clarsimp?)
    apply (clarsimp simp: obj_at_def ct_in_state_def pred_tcb_at_def vs_all_heap_simps)
    apply (frule_tac t="cur_thread s" in sym_refs_RecvEP_ipc_queued_thread; blast?, simp?)
    apply (clarsimp simp: vs_all_heap_simps)
   apply fastforce

  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp simp: when_def pred_conj_def)
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: refill_unblock_check_pred_tcb_at
                       [simplified pred_tcb_at_def, where proj="itcb_sched_context", simplified])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if)
   apply (wpsimp wp: possible_switch_to_ct_not_queued)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if)
   apply (wpsimp wp: handle_timeout_ct_not_queued
               simp: pred_tcb_at_def obj_at_def ct_in_state_def vs_all_heap_simps)
  apply (wpsimp wp: postpone_ct_not_queued)
  apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_eq_normalise)
  apply (frule (1) heap_refs_retractD)
  apply (clarsimp simp: vs_all_heap_simps)
  done

lemma handle_invocation_scheduler_act_sane[wp]:
  "\<lbrace>schact_is_rct and invs and ct_active\<rbrace>
   handle_invocation False False True True reply_cptr
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wpsimp wp: hoare_drop_imp ct_in_state_set hoare_drop_impE)
      apply (rule validE_cases_valid, clarsimp)
      apply (subst validE_R_def[symmetric])
      apply (rule_tac Q'="\<lambda>rv s. simple_sched_action s \<and> cur_thread s = thread
                                  \<and> st_tcb_at active thread s \<and> invs s
                                  \<and> valid_invocation rv s"
                   in hoare_post_imp_R[rotated])
       apply (clarsimp cong: conj_cong)
       apply (intro conjI)
        apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
        apply (erule if_live_then_nonz_cap_invs, assumption)
        apply (fastforce simp: live_def split: thread_state.split)
       apply (rule fault_tcbs_valid_states_active, clarsimp)
       apply blast
      apply (wp decode_inv_wf)
     apply (wpsimp wp: hoare_vcg_conj_lift hoare_drop_imps)
     apply (rule validE_cases_valid, clarsimp)
     apply (subst validE_R_def[symmetric])
     apply wpsimp+
  apply (intro conjI)
     apply (erule schact_is_rct_sane)
    apply (erule schact_is_rct_simple)
   apply (simp add: pred_tcb_at_def obj_at_def ct_in_state_def)
  apply (erule invs_valid_objs)
  done

lemma postpone_not_in_release_q_other:
  "\<lbrace>not_in_release_q t and sc_tcb_sc_at (\<lambda>sc_tcb. sc_tcb \<noteq> Some t) sc_ptr\<rbrace>
   postpone sc_ptr
   \<lbrace>\<lambda>_. not_in_release_q t\<rbrace>"
  apply (simp add: postpone_def)
  apply (wpsimp wp: tcb_release_enqueue_not_in_release_q get_sc_obj_ref_wp)
  by (simp add: sc_at_ppred_def obj_at_def)

lemma sched_context_resume_not_in_release_q_other:
  "\<lbrace>not_in_release_q t and sc_tcb_sc_at (\<lambda>sc_tcb. sc_tcb \<noteq> Some t) sc_ptr\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. not_in_release_q t\<rbrace>"
  apply (simp add: sched_context_resume_def)
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps hoare_vcg_if_lift
                 postpone_not_in_release_q_other
           simp: if_fun_split)

lemma sched_context_bind_tcb_not_in_release_q_other:
  "\<lbrace>not_in_release_q t and K (t \<noteq> tcb_ptr)\<rbrace>
   sched_context_bind_tcb sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. not_in_release_q t\<rbrace>"
  apply (simp add: sched_context_bind_tcb_def)
  by (wpsimp wp: sched_context_resume_not_in_release_q_other sc_tcb_update_sc_tcb_sc_at)

lemma sched_context_bind_tcb_not_queued_other:
  "\<lbrace>not_queued t and K (t \<noteq> tcb_ptr) and scheduler_act_not t\<rbrace>
   sched_context_bind_tcb sc_ptr tcb_ptr
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: sched_context_bind_tcb_def)
  by (wpsimp wp: reschedule_required_not_queued tcb_sched_enqueue_not_queued update_sched_context_wp
                 sched_context_resume_not_queued sc_tcb_update_sc_tcb_sc_at
                 hoare_vcg_all_lift hoare_drop_imps
           simp: is_schedulable_def vs_all_heap_simps)

lemma sched_context_yield_to_not_in_release_q_other:
  "\<lbrace>not_in_release_q t and sc_tcb_sc_at (\<lambda>sctcb. sctcb \<noteq> Some t) sc_ptr\<rbrace>
   sched_context_yield_to sc_ptr args
   \<lbrace>\<lambda>_. not_in_release_q t\<rbrace>"
  apply (simp add: sched_context_yield_to_def)
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps get_sc_obj_ref_wp
                 sched_context_resume_not_in_release_q_other)

lemma sched_context_update_consumed_sc_yf_sc_at[wp]:
  "sched_context_update_consumed sc_ptr \<lbrace>sc_yf_sc_at P sc_ptr \<rbrace>"
  unfolding sched_context_update_consumed_def
  by (wpsimp wp: update_sched_context_wp
           simp: sc_at_pred_n_def obj_at_def)

crunches sched_context_resume
  for sched_context_at[wp]: "\<lambda>s. \<exists>n. ko_at (SchedContext sc n) sc_ptr s"
  (wp: mapM_wp' get_simple_ko_wp hoare_drop_imps)

lemma sched_context_yield_to_not_queued_other:
  "\<lbrace>\<lambda>s. ct_not_queued s
        \<and> sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s
        \<and> scheduler_act_not (cur_thread s) s\<rbrace>
   sched_context_yield_to sc_ptr args
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (simp add: sched_context_yield_to_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply ((wpsimp wp: update_sched_context_wp hoare_drop_imps
                simp: when_def maybeM_def bind_assoc set_tcb_obj_ref_def get_tcb_obj_ref_def
           | wps)+)[1]

  apply (clarsimp simp: get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])

  apply (rule hoare_seq_ext_skip)
   apply ((wpsimp wp: sched_context_resume_not_queued | wps)+)[1]
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def vs_all_heap_simps)

  apply (rule_tac Q="\<lambda>s. sc_tcb_sc_at ((=) (Some tcb_ptr)) sc_ptr s
                         \<and> ct_not_queued s
                         \<and> sc_tcb_sc_at (\<lambda>sctcb. \<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s) sc_ptr s
                         \<and> scheduler_act_sane s"
               in hoare_weaken_pre[rotated])
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def ct_in_state_def)

  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, ((wpsimp | wps)+)[1])
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
  apply (rule hoare_if)
   apply ((wpsimp wp: tcb_sched_enqueue_not_queued tcb_sched_dequeue_ct_not_queued
                simp: sc_at_pred_n_def obj_at_def ct_in_state_def
           | wps)+)[1]
  apply (wpsimp wp: update_sched_context_wp tcb_sched_dequeue_ct_not_queued
              simp: sc_at_pred_n_def obj_at_def ct_in_state_def
         | wps)+
  done

crunches sched_context_bind_tcb, sched_context_yield_to, invoke_irq_handler
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps)

crunches sched_context_unbind_all_tcbs
  for not_in_release_queue[wp]: "not_in_release_q t"

lemma invoke_sched_context_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and valid_sched_context_inv i and schact_is_rct and invs\<rbrace>
   invoke_sched_context i
   \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  apply (simp add: invoke_sched_context_def)
  apply (cases i; simp)
      apply (find_goal \<open>match premises in \<open>_ = InvokeSchedContextBind _ _\<close> \<Rightarrow> \<open>-\<close>\<close>)
      apply (wpsimp wp: sched_context_bind_tcb_not_in_release_q_other | wps)+
      apply (clarsimp dest!: invs_cur_sc_tcb_symref simp: pred_tcb_at_def obj_at_def)
     apply (find_goal \<open>match premises in \<open>_ = InvokeSchedContextYieldTo _ _\<close> \<Rightarrow> \<open>-\<close>\<close>)
     apply (wpsimp wp: sched_context_yield_to_not_in_release_q_other | wps)+
     apply (clarsimp simp: sc_at_ppred_def obj_at_def)
    apply (wpsimp | wps)+
  done

lemma invoke_sched_context_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and valid_sched_context_inv i and schact_is_rct and invs\<rbrace>
   invoke_sched_context i
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (simp add: invoke_sched_context_def)
  apply (cases i; simp)
      apply (find_goal \<open>match premises in \<open>_ = InvokeSchedContextBind _ _\<close> \<Rightarrow> \<open>-\<close>\<close>)
      apply (wpsimp wp: sched_context_bind_tcb_not_queued_other | wps)+
       apply (fastforce dest!: invs_cur_sc_tcb_symref simp: pred_tcb_at_def obj_at_def)
     apply (find_goal \<open>match premises in \<open>_ = InvokeSchedContextYieldTo _ _\<close> \<Rightarrow> \<open>-\<close>\<close>)
     apply (wpsimp wp: sched_context_yield_to_not_queued_other | wps)+
  done

crunches invoke_irq_control, invoke_irq_handler
  for not_in_release_queue[wp]: "not_in_release_q t :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

crunches invoke_irq_control
  for not_queued[wp]: "not_queued t :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps)

lemma cap_delete_one_not_queued[wp]:
  "\<lbrace>valid_objs and sym_refs \<circ> state_refs_of and st_tcb_at active t and scheduler_act_not t
    and not_queued t\<rbrace>
   cap_delete_one slot
   \<lbrace>\<lambda>_. not_queued t :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: fast_finalise_not_queued empty_slot_valid_sched get_object_wp simp: get_cap_def)

lemma invoke_irq_handler_not_queued[wp]:
  "\<lbrace>valid_objs and sym_refs \<circ> state_refs_of and st_tcb_at active t and scheduler_act_not t
    and not_queued t\<rbrace>
   invoke_irq_handler iv
   \<lbrace>\<lambda>_. not_queued t :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (cases iv; wpsimp)

crunches set_domain
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma set_domain_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> set_domain thread domain \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: set_domain_def)
  apply (rule hoare_seq_ext[OF _gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp wp: tcb_sched_dequeue_ct_not_queued)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (wpsimp wp: tcb_sched_enqueue_not_queued | wps)+
  done

lemma invoke_domain_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> invoke_domain thread domain \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  unfolding invoke_domain_def by wpsimp

lemma perform_invocation_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and invs and ct_active and valid_invocation i
    and schact_is_rct and K (safe_invocation i)\<rbrace>
   perform_invocation block call can_donate i
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases i; (wpsimp | wps)+)
   apply (rule valid_validE)
   apply (wps, wpsimp+)
  done

lemma perform_invocation_ct_not_queued[wp]:
  "\<lbrace>ct_not_in_release_q and ct_not_queued and invs and ct_active and valid_invocation i
    and schact_is_rct and K (safe_invocation i)\<rbrace>
   perform_invocation block call can_donate i
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases i; (wpsimp wp: send_ipc_not_queued | wps)+)

      \<comment> \<open>Discharge preconditions for InvokeEndpoint\<close>
      apply (intro conjI)
       apply (erule schact_is_rct_sane)
      apply (clarsimp simp: obj_at_def is_ep_def vs_all_heap_simps)
      apply (frule RecvEP_queued_ipc_queued_thread, fastforce)
      apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def vs_all_heap_simps)

find_theorems send_signal ct_not_queued

     \<comment> \<open>Discharge preconditions for InvokeReply\<close>
     apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def is_tcb_def)

    \<comment> \<open>InvokeIRQControl and InvokeIRQHandler\<close>
    apply (rule valid_validE)
    apply (wps, wpsimp)+
   apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def)+
  done

lemma handle_invocation_first_phase_ct_not_in_release_q[wp]:
  "\<lbrace>ct_not_in_release_q and invs and ct_active and schact_is_rct
    and (\<lambda>s. is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s)\<rbrace>
   handle_invocation calling blocking can_donate True reply_cptr
   \<lbrace>\<lambda>_. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_invocation_def split_def ts_Restart_case_helper)
  apply (wpsimp wp: syscall_valid set_thread_state_ct_st hoare_drop_imps
                    sts_schedulable_scheduler_action)
  apply (auto simp: ct_in_state_def fault_tcbs_valid_states_active
              dest: invs_fault_tcbs_valid_states
              elim: st_tcb_ex_cap)
  done

lemma reply_push_ct_in_state:
  "\<lbrace>ct_in_state P and (\<lambda>s. thread = cur_thread s \<longrightarrow> (\<forall>y. P (BlockedOnReply y)))\<rbrace>
   reply_push thread x21 y can_donate
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding reply_push_def
  by (wpsimp wp: sts_ctis_neq hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift
                    get_simple_ko_wp)

lemma handle_invocation_first_phase_ct_not_queued[wp]:
  "\<lbrace>ct_not_in_release_q and ct_not_queued and invs and ct_active and schact_is_rct
    and (\<lambda>s. is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s)\<rbrace>
   handle_invocation False False can_donate True reply_cptr
   \<lbrace>\<lambda>_. ct_not_queued :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_invocation_def split_def ts_Restart_case_helper)
  apply (wpsimp wp: syscall_valid set_thread_state_ct_st hoare_drop_imps
                    sts_schedulable_scheduler_action)
  apply (auto simp: ct_in_state_def fault_tcbs_valid_states_active
              dest: invs_fault_tcbs_valid_states
              elim: st_tcb_ex_cap)
  done

lemma send_ipc_ct_in_state:
  "\<lbrace>ct_in_state P and
    (\<lambda>s. (thread = cur_thread s \<longrightarrow> block \<longrightarrow> (\<forall>pl. P (BlockedOnSend epptr pl)))
         \<and> (\<forall>st. is_BlockedOnReceive st \<longrightarrow> P st \<longrightarrow> P Running \<and> P Inactive)
         \<and> (thread = cur_thread s \<longrightarrow>
            ((call \<or> fault_tcb_at bound (cur_thread s) s) \<longrightarrow> (\<forall>y. P (BlockedOnReply y))))
         \<and> (thread = cur_thread s \<longrightarrow> P Inactive)):: 'state_ext state \<Rightarrow> _\<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate thread epptr
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding send_ipc_def
  apply (wpsimp wp: sts_ctis_neq)
            apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift get_tcb_obj_ref_wp)
           apply (rule_tac Q="\<lambda>a b. ct_in_state P b \<and> (cur_thread b = x21 \<longrightarrow>  P Running)" in hoare_strengthen_post[rotated])
            apply clarsimp
           apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_all_lift  hoare_vcg_imp_lift' reply_push_ct_in_state sts_ctis_neq)
          apply (wpsimp wp: thread_get_wp')+
        apply (rule_tac Q="\<lambda>a b. ct_in_state P b
                                 \<and> (cur_thread b = x21 \<longrightarrow> P Running)
                                 \<and> (thread = cur_thread b \<longrightarrow> (call \<or> fault_tcb_at bound thread b)
                                    \<longrightarrow> (\<forall>y. P (BlockedOnReply y)) \<and> (\<not>can_grant \<longrightarrow> (P Inactive)))" in hoare_strengthen_post[rotated])
         apply (auto simp: pred_tcb_at_def obj_at_def)[1]
        apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_all_lift reply_unlink_tcb_ct_in_state_weak hoare_vcg_imp_lift')
       apply clarsimp
       apply (rule_tac Q="\<lambda>a b. ct_in_state P b
                                \<and> (cur_thread b = x21 \<longrightarrow> (P Running \<and> P Inactive))
                                \<and> (thread = cur_thread b \<longrightarrow> (call \<or> fault_tcb_at bound thread b)
                                   \<longrightarrow> (\<forall>y. P (BlockedOnReply y)))
                                \<and> (thread = cur_thread b \<longrightarrow> (P Inactive))" in hoare_strengthen_post[rotated])
        apply (clarsimp simp: pred_tcb_at_def obj_at_def)[1]
       apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_all_lift reply_unlink_tcb_ct_in_state_weak hoare_vcg_imp_lift')
      apply (wpsimp wp: gts_wp)+
    apply wps
    apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_all_lift reply_unlink_tcb_ct_in_state_weak hoare_vcg_imp_lift')
   apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps ct_in_state_def is_BlockedOnReceive_def)
  apply fastforce
  done

lemma handle_timeout_ct_not_BlockedOnNtfn:
  "handle_timeout tptr ex \<lbrace>ct_not_BlockedOnNtfn :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def send_fault_ipc_def
  by (wpsimp wp: send_ipc_ct_in_state thread_set_ct_in_state)

lemma handle_timeout_ct_in_state:
  "\<lbrace>ct_in_state P
    and (\<lambda>s. tptr = cur_thread s)
    and (\<lambda>_. (\<forall>pl x. P (BlockedOnSend x pl))
             \<and> (\<forall>st. is_BlockedOnReceive st \<longrightarrow> P st \<longrightarrow> P Running)
             \<and> (\<forall>y. P (BlockedOnReply y))
             \<and> P Inactive)\<rbrace>
   handle_timeout tptr ex
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def send_fault_ipc_def
  apply (wpsimp wp: send_ipc_ct_in_state thread_set_wp thread_set_ct_in_state
              simp: send_fault_ipc_def)
  apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps vs_all_heap_simps dest!: get_tcb_SomeD)
  done

lemma end_timeslice_ct_not_BlockedOnNtfn[wp]:
  "end_timeslice t \<lbrace>ct_not_BlockedOnNtfn :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  by (wpsimp wp: hoare_drop_imp handle_timeout_ct_not_BlockedOnNtfn)

lemma end_timeslice_ct_in_state:
  "\<lbrakk>P Inactive; P Running; \<forall>y. P (BlockedOnReply y); \<forall>x z. P (BlockedOnSend x z)\<rbrakk>
   \<Longrightarrow> end_timeslice t \<lbrace>ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  by (wpsimp wp: hoare_drop_imp handle_timeout_ct_in_state)

lemma charge_budget_ct_not_BlockedOnNtfn[wp]:
  "charge_budget consumed t \<lbrace>ct_not_BlockedOnNtfn :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp)

lemma charge_budget_ct_in_state:
  "\<lbrakk>P Inactive; P Running; \<forall>y. P (BlockedOnReply y); \<forall>x z. P (BlockedOnSend x z)\<rbrakk>
   \<Longrightarrow> charge_budget consumed t \<lbrace>ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding charge_budget_def
  by (wpsimp wp: hoare_drop_imp end_timeslice_ct_in_state)

lemma check_budget_ct_not_BlockedOnNtfn[wp]:
  "check_budget \<lbrace>ct_not_BlockedOnNtfn :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: hoare_drop_imp)

lemma check_budget_ct_in_state:
  "\<lbrakk>P Inactive; P Running; \<forall>y. P (BlockedOnReply y); \<forall>x z. P (BlockedOnSend x z)\<rbrakk>
   \<Longrightarrow> check_budget \<lbrace>ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding check_budget_def
  by (wpsimp wp: hoare_drop_imp charge_budget_ct_in_state)

lemma valid_sched_ct_not_queued:
  "\<lbrakk>valid_sched s; schact_is_rct s\<rbrakk> \<Longrightarrow> ct_not_queued s"
  by (fastforce simp: valid_sched_def ct_not_in_q_def schact_is_rct_def)

lemma ct_not_blocked_cur_sc_not_blocked_trivial:
  "cur_sc_tcb_only_sym_bound s \<and> ct_not_blocked s \<Longrightarrow> cur_sc_not_blocked s"
  by (rule ct_not_blocked_cur_sc_not_blocked[OF strengthen_cur_sc_chargeable]; clarsimp)

end

context DetSchedSchedule_AI_det_ext begin

(* These need to be resolved before we can say that we have solved handle_event_valid_sched.
   We now believe that the first statement is provable and that the second is probably
   provable. In either case, we need to prove these lemmas, or delete them and
   solve handle_event_valid_sched another way. *)
lemma handle_invocation_ct_conditions_temp[wp]:
  "handle_invocation False False True True reply_cptr \<lbrace>\<lambda>s :: det_state. released_if_bound_sc_tcb_at (cur_thread s) s\<rbrace>"
  sorry (* handle_invocation_ct_conditions_temp *)

end

context DetSchedSchedule_AI begin

lemma refill_bounded_helper:
  "valid_refills (cur_sc s) s
   \<Longrightarrow> 2*unat MAX_SC_PERIOD \<le> unat max_time
   \<Longrightarrow> (\<forall>sc. (\<exists>n. kheap s (cur_sc s) = Some (SchedContext sc n)) \<longrightarrow>
                   unat (r_amount (refill_hd sc)) + unat MAX_SC_PERIOD \<le> unat max_time)"
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (clarsimp simp: vs_all_heap_simps valid_refills_def)
  apply (subst word_le_nat_alt[symmetric], rule valid_refills_r_amount_bounded_max_sc_period)
  apply (clarsimp simp: sc_valid_refills_def)
  done

lemma to_handle_final_time_obligationsAA:
  "\<lbrace>\<lambda>s. pred_next_time (\<lambda>nt. unat nt + unat MAX_SC_PERIOD \<le> unat max_time) s\<rbrace>
    update_time_stamp
   \<lbrace>\<lambda>_ s. unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_wp])
  apply (rule_tac hoare_seq_ext)
  apply wpsimp
  by (fastforce simp: valid_def is_next_time_def pred_next_time_def)


lemma pred_next_time_trivial[simp]:
  "pred_next_time \<top> s = True"
  by (clarsimp simp: pred_next_time_def)

lemma update_time_stamp_cur_time[wp]:
  "\<lbrace>\<lambda>s. pred_next_time Q s\<rbrace>
    update_time_stamp
   \<lbrace>\<lambda>_ s. Q (cur_time s)\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_wp])
  apply (rule_tac hoare_seq_ext)
  apply wpsimp
  by (fastforce simp: valid_def is_next_time_def pred_next_time_def)

lemma update_time_stamp_consumed_time_bounded[wp]:
  "\<lbrace>consumed_time_bounded and valid_machine_time\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_. consumed_time_bounded :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac P="(consumed_time_bounded and (\<lambda>s. cur_time s = prev_time))"
          in dmo_getCurrentTime_wp)
    apply (clarsimp simp: valid_def is_next_time_def pred_next_time_def consumed_time_bounded_def)
    apply (subst add_diff_eq[symmetric])
    apply (subst unat_add_lem', overflow_hammer)
     apply (subst unat_sub, simp)
     apply (metis (no_types, hide_lams) add_mono_thms_linordered_semiring(3)
            le_add_diff_inverse le_trans max_word_max unat_arith_simps(1) )
    apply (subst unat_sub, simp)
    apply (subst add_diff_assoc, overflow_hammer)
    apply linarith
   apply wpsimp
  apply clarsimp
  done

crunches preemption_point
  for consumed_time_bounded[wp]: "consumed_time_bounded :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps rule: preemption_point_inv simp: crunch_simps ignore_del: preemption_point)

crunches cancel_badged_sends
  for cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps filterM_preserved simp: crunch_simps)

crunches cap_revoke
  for cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _"
  and consumed_time_bounded[wp]: "consumed_time_bounded :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps rule: cap_revoke_preservation2 simp: crunch_simps)

crunches perform_invocation
  for cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv get_simple_ko_wp simp: crunch_simps)

crunches handle_fault, reply_from_kernel, lookup_cap_and_slot
  for cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _"
  and consumed_time_bounded[wp]: "consumed_time_bounded :: 'state_ext state \<Rightarrow> _"

lemma handle_invocation_cur_time[wp]:
  "handle_invocation a b c d cptr
   \<lbrace>(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def
  by (wpsimp wp: syscall_valid hoare_drop_imp hoare_drop_impE)

lemma handle_call_cur_time[wp]:
  "handle_call \<lbrace>(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_call_def
   by wpsimp

crunches handle_send, handle_recv, handle_yield, check_budget_restart, handle_interrupt
  for cur_time[wp]: "(\<lambda>s. P (cur_time s)) :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

(* FIXME: move *)
lemma consumed_time_detype[simp]:
  "consumed_time (detype r s) = consumed_time s"
  by (simp add: detype_def)

crunches perform_invocation
  for consumed_time_bounded[wp]: "consumed_time_bounded :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv get_simple_ko_wp mapME_x_wp_inv filterM_preserved simp: crunch_simps)

crunches handle_call, handle_send, handle_recv, handle_yield, check_budget_restart, handle_interrupt
  for consumed_time_bounded[wp]: "consumed_time_bounded :: 'state_ext state \<Rightarrow> _"
  (wp: syscall_valid crunch_wps simp: crunch_simps ignore: syscall)

lemma update_time_stamp_cur_sc_offset_ready_cs[wp]:
  "\<lbrace>valid_machine_time and (\<lambda>s. cur_sc_offset_ready (consumed_time s) (s:: 'state_ext state))\<rbrace>
   update_time_stamp
   \<lbrace>\<lambda>_ s. cur_sc_offset_ready (consumed_time s) s\<rbrace>"
  unfolding update_time_stamp_def
  apply (rule_tac hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac P="\<lambda>s. cur_sc_offset_ready (consumed_time s) s \<and> cur_time s = prev_time"
          in dmo_getCurrentTime_wp)
    apply (clarsimp simp: vs_all_heap_simps refill_ready_no_overflow_def)
    apply (rename_tac sc n)
    apply (rule_tac y="unat (r_time (refill_hd sc)) + unat (consumed_time s) + unat (rv - cur_time s)" in order_trans)
     apply clarsimp
     apply (subst add_diff_eq[symmetric])
     apply (rule unat_plus_gt)
    apply (subst unat_sub, assumption)
    apply (subst diff_add_assoc[symmetric])
     apply overflow_hammer
    apply (clarsimp simp: le_diff_conv)
   apply wpsimp
  apply clarsimp
  done

lemma strengthen_consumed_time_bound:
  "unat (cur_time s) + unat MAX_SC_PERIOD \<le> unat max_time
   \<and> unat (consumed_time s) \<le> unat (cur_time s)
   \<Longrightarrow> unat (consumed_time s) + unat MAX_SC_PERIOD \<le> unat max_time"
  by linarith

end

context DetSchedSchedule_AI_handle_hypervisor_fault_det_ext begin

lemma check_budget_restart_valid_sched_weaker:
  "\<lbrace>valid_sched
    and invs
    and ct_not_in_release_q
    and ct_not_queued
    and schact_is_rct
    and ct_released
    and current_time_bounded 2
    and consumed_time_bounded
    and cur_sc_active
    and ct_not_blocked
    and (\<lambda>s. valid_refills (cur_sc s) s \<and>
   cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>rv s::det_ext state. \<not>rv \<longrightarrow> valid_sched s\<rbrace>"
  apply (wpsimp wp: check_budget_restart_valid_sched
              simp: consumed_time_bounded_def current_time_bounded_def)
  apply (erule (2) ct_not_blocked_cur_sc_not_blocked[OF invs_cur_sc_chargeableE])
  done

lemma check_budget_valid_sched_weaker:
  "\<lbrace>valid_sched
    and invs
    and ct_not_in_release_q and ct_not_queued
    and scheduler_act_sane and cur_sc_chargeable
    and consumed_time_bounded
    and current_time_bounded 2
    and cur_sc_active
    and ct_not_blocked
    and (\<lambda>s. valid_refills (cur_sc s) s)
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)\<rbrace>
   check_budget
   \<lbrace>\<lambda>_. valid_sched::det_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: check_budget_valid_sched simp: invs_retract_tcb_scps[THEN heap_refs_retract_heap_refs_retract_at])
  apply (erule (1) ct_not_blocked_cur_sc_not_blocked)
  done

lemma handle_event_valid_sched:
  "\<lbrace>invs
    and valid_sched
    and ct_in_state activatable
    and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
    and cur_sc_active
    and ct_not_in_release_q
    and schact_is_rct
    and ready_or_release
    and valid_reply_scs
    and (\<lambda>s. cur_sc_budget_sufficient s)
    and ct_released and (\<lambda>s. valid_refills (cur_sc s) s)
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
    and next_time_bounded 2
    and consumed_time_bounded\<rbrace>
   handle_event e
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  supply check_budget_restart_true [wp]
     and next_time_bounded_weaken[elim!]
  apply (cases e, simp_all)
  (* SyscallEvent *)
       subgoal for syscall
         apply (case_tac syscall, simp_all add: handle_send_def handle_call_def liftE_bindE)
                   apply (wpsimp wp: handle_invocation_valid_sched check_budget_restart_valid_sched_weaker)+
                   apply (fastforce elim!: valid_sched_ct_not_queued active_from_running)
                  apply(wpsimp wp: handle_invocation_valid_sched
                                   handle_recv_valid_sched check_budget_restart_valid_sched_weaker
                             simp: is_schedulable_bool_def2 active_sc_tcb_at_fold)
                  apply (fastforce dest: valid_sched_ct_not_queued
                                   elim: active_from_running
                                   simp: runnable_eq_active pred_next_time_def released_sc_tcb_at_def
                                         active_sc_tcb_at_fold ct_in_state_def2[symmetric])
                 apply (wpsimp wp: handle_invocation_valid_sched
                                   handle_recv_valid_sched check_budget_restart_valid_sched_weaker
                             simp: is_schedulable_bool_def2 active_sc_tcb_at_fold)+
                  apply (fastforce dest: valid_sched_ct_not_queued
                                   elim: active_from_running
                                   simp: runnable_eq_active pred_next_time_def released_sc_tcb_at_def
                                         active_sc_tcb_at_fold ct_in_state_def2[symmetric])
                apply (wpsimp wp: handle_invocation_valid_sched
                                  handle_recv_valid_sched check_budget_restart_valid_sched_weaker
                            simp: is_schedulable_bool_def2 active_sc_tcb_at_fold)+
                  apply (fastforce dest: valid_sched_ct_not_queued
                                   elim: active_from_running
                                   simp: runnable_eq_active pred_next_time_def released_sc_tcb_at_def
                                         active_sc_tcb_at_fold ct_in_state_def2[symmetric])
               apply (wpsimp wp: handle_invocation_valid_sched check_budget_restart_valid_sched_weaker )
               apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                                 elim: active_from_running)
              apply (wpsimp wp: handle_invocation_valid_sched check_budget_restart_valid_sched_weaker)
              apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                                elim: active_from_running)
             apply (wpsimp wp: handle_recv_valid_sched check_budget_restart_valid_sched_weaker)
             apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                               elim: active_from_running)
            apply (wpsimp wp: handle_yield_valid_sched check_budget_restart_valid_sched_weaker
                   | strengthen refill_bounded_helper)+
            apply (auto elim!: valid_sched_ct_not_queued elim: invs_cur_sc_chargeableE
                     intro!: next_time_bounded_weaken1 next_time_bounded_weaken2
                     simp: released_sc_tcb_at_def runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                          tcb_at_kh_simps vs_all_heap_simps)[1]
           apply (wpsimp wp: handle_recv_valid_sched check_budget_restart_valid_sched_weaker)
           apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                             elim: active_from_running)
          apply (wpsimp wp: handle_recv_valid_sched check_budget_restart_valid_sched_weaker)
         apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                           elim: active_from_running)
        apply (wpsimp wp: handle_recv_valid_sched check_budget_restart_valid_sched_weaker)
        apply (fastforce elim!: valid_sched_ct_not_queued simp: runnable_eq_active released_sc_tcb_at_def ct_in_state_def
                          elim: active_from_running)
       done
         (* UnknownSyscall *)
         apply (wpsimp wp: handle_fault_valid_sched check_budget_restart_valid_sched_weaker
                           hoare_vcg_if_lift2 hoare_vcg_disj_lift)
         apply (frule active_from_running, clarsimp)
         apply (clarsimp simp: valid_fault_def ct_in_state_def2[symmetric] pred_next_time_def)
         apply (strengthen valid_sched_valid_machine_time schact_is_rct_sane valid_sched_ct_not_queued, simp)
         apply (clarsimp simp: ct_active_imp_not_timeout is_timeout_fault_def)
        (* UserLevelFault *)
        apply (wpsimp wp: handle_fault_valid_sched check_budget_restart_valid_sched_weaker
                          hoare_vcg_if_lift2 hoare_vcg_disj_lift)
        apply (frule active_from_running, clarsimp)
        apply (clarsimp simp: valid_fault_def ct_in_state_def2[symmetric])
        apply (strengthen valid_sched_valid_machine_time schact_is_rct_sane valid_sched_ct_not_queued, simp)
        apply (clarsimp simp: ct_active_imp_not_timeout is_timeout_fault_def)
    (* Interrupt *)
    subgoal
      apply wpsimp
         apply (wpsimp wp: handle_interrupt_valid_sched check_budget_restart_valid_sched_weaker)
         apply (wpsimp wp: check_budget_valid_sched_weaker hoare_vcg_all_lift hoare_vcg_imp_lift')
       apply(rule_tac Q="\<lambda>_. valid_sched and invs and ct_not_in_release_q
                         and ct_in_state activatable
                         and cur_sc_active
                         and (\<lambda>s.  cur_sc_offset_ready (consumed_time s) s)
                         and consumed_time_bounded
                         and schact_is_rct and ct_not_queued
                         and (\<lambda>s. valid_refills (cur_sc s) s)
                         and current_time_bounded 2" in hoare_strengthen_post[rotated])
         apply (clarsimp simp: if_split)
         apply (intro conjI allI impI)
                apply fastforce
               apply (fastforce intro: invs_cur_sc_chargeableE)
              apply (fastforce elim: ct_in_state_weaken)
             apply fastforce
            apply (fastforce intro: invs_cur_sc_chargeableE)
           apply (fastforce elim: ct_in_state_weaken)
          apply fastforce
         apply (fastforce elim!: current_time_bounded_strengthen)
        apply wpsimp
       apply (wpsimp, clarsimp simp: ct_in_state_def)
      apply (fastforce elim!: valid_sched_ct_not_queued elim: invs_cur_sc_chargeableE ct_in_state_weaken
                       intro!: next_time_bounded_current_time_bounded)
      done
  (* VMFaultEvent *)
   apply (wpsimp wp: handle_fault_valid_sched check_budget_restart_valid_sched_weaker
                     hoare_vcg_if_lift2 hoare_vcg_disj_lift)
   apply (frule active_from_running)
   apply (clarsimp simp: valid_fault_def ct_in_state_def2[symmetric])
   apply (strengthen valid_sched_valid_machine_time schact_is_rct_sane valid_sched_ct_not_queued ct_runnable_ct_not_blocked, simp)
  (* HypervisorEvent *)
  apply (wpsimp wp: handle_hyp_fault_valid_sched check_budget_restart_valid_sched_weaker
                    hoare_vcg_if_lift2 hoare_vcg_disj_lift)
  apply (frule active_from_running)
  apply (fastforce elim!: valid_sched_ct_not_queued ct_in_state_weaken simp: ct_in_state_def valid_fault_def)
  done

crunches activate_thread, schedule_choose_new_thread, awaken
  for valid_list[wp]: valid_list
  (wp: crunch_wps)

lemma schedule_valid_list[wp]: "\<lbrace>valid_list\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: Schedule_A.schedule_def)
  apply (wp add: tcb_sched_action_valid_list alternative_wp select_wp gts_wp hoare_drop_imps
                 is_schedulable_wp hoare_vcg_all_lift
         | wpc | simp)+
  done

lemma call_kernel_valid_list[wp]: "\<lbrace>valid_list\<rbrace> call_kernel e \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: call_kernel_def)
  by (wpsimp wp: is_schedulable_wp hoare_drop_imps hoare_vcg_all_lift)+

lemma handle_event_consumed_time_bounded[wp]:
  "\<lbrace>consumed_time_bounded and valid_machine_time\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. consumed_time_bounded :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp; wpsimp wp: hoare_drop_imp hoare_drop_impE cong: conj_cong)
  done

lemma handle_event_current_time_bounded[wp]:
  "\<lbrace>next_time_bounded k and valid_machine_time\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. current_time_bounded k :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp; wpsimp wp: hoare_drop_imp hoare_drop_impE cong: conj_cong)
  apply (erule (1) next_time_bounded_current_time_bounded)
  done

end

context DetSchedSchedule_AI begin

lemma reply_unlink_tcb_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tp\<rbrace>
     reply_unlink_tcb tp rp
   \<lbrace> \<lambda>_. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def
               wp: set_thread_state_valid_release_q gts_wp get_simple_ko_wp)

lemma reply_remove_tcb_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tp\<rbrace>
   reply_remove_tcb tp rp
   \<lbrace> \<lambda>_. valid_release_q:: 'state_ext state \<Rightarrow> _ \<rbrace>"
  by (wpsimp simp: reply_remove_tcb_def wp: hoare_drop_imp)

lemma blocked_cancel_ipc_valid_release_q[wp]:
  "\<lbrace> valid_release_q and not_in_release_q tptr\<rbrace>
     blocked_cancel_ipc state tptr reply_opt
   \<lbrace> \<lambda>_. valid_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: blocked_cancel_ipc_def)
  by (wpsimp wp: set_thread_state_valid_release_q hoare_drop_imp)

crunches handle_interrupt
for ct_active[wp]: "ct_active::'state_ext state \<Rightarrow> _"

lemma call_kernel_valid_sched_check_budget_helper:
  "\<lbrace>valid_sched
    and invs
    and schact_is_rct
    and cur_sc_chargeable
    and ct_not_in_release_q
    and ct_not_queued
    and current_time_bounded 2
    and consumed_time_bounded
    and cur_sc_active
    and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
    and cur_sc_not_blocked\<rbrace>
   check_budget
   \<lbrace>\<lambda>_ s::'state_ext state.
           valid_sched s \<and>
           invs s \<and>
           (the irq \<in> non_kernel_IRQs \<longrightarrow>
            scheduler_act_sane s \<and> ct_not_queued s \<and> ct_not_in_release_q s)\<rbrace>"
  apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def) (* FIXME RT *)
  apply (wpsimp wp: hoare_vcg_conj_lift reschedule_valid_sched_const get_sched_context_wp
                    hoare_drop_imps hoare_vcg_all_lift charge_budget_invs charge_budget_valid_sched)
  apply (clarsimp simp: invs_retract_tcb_scps[THEN heap_refs_retract_heap_refs_retract_at])
  apply (fastforce elim: current_time_bounded_strengthen intro: consumed_time_bounded_helper)
  done

lemma call_kernel_valid_sched_charge_budget_helper:
  "\<lbrace>valid_sched
    and invs
    and ct_not_in_release_q and ct_not_queued
    and cur_sc_chargeable and scheduler_act_sane
    and cur_sc_not_blocked
    and current_time_bounded 2
    and cur_sc_active
    and (\<lambda>s. unat consumed + unat MAX_SC_PERIOD \<le> unat max_time)
    and (\<lambda>s. (\<forall>sc. (\<exists>n. kheap s (cur_sc s) = Some (SchedContext sc n)) \<longrightarrow>
                    (sc_refill_ready (cur_time s) sc \<longrightarrow>
                     r_amount (refill_hd sc) < consumed) \<longrightarrow>
                    cur_sc_offset_ready consumed s))\<rbrace>
  charge_budget consumed False
  \<lbrace>\<lambda>_ s:: 'state_ext state.
           valid_sched s \<and>
           invs s \<and>
           (the irq \<in> non_kernel_IRQs \<longrightarrow>
            scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>"
   apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def)
   by (wpsimp wp: hoare_vcg_conj_lift reschedule_valid_sched_const get_sched_context_wp
                  hoare_drop_imps hoare_vcg_all_lift charge_budget_invs charge_budget_valid_sched
            simp: invs_retract_tcb_scps[THEN heap_refs_retract_heap_refs_retract_at]
                  obj_at_kh_kheap_simps pred_map_eq_normalise)

lemma preemption_point_valid_sched_pred[wp]:
  "preemption_point \<lbrace>valid_sched_pred_strong P\<rbrace>"
  unfolding preemption_point_def
  by (wpsimp simp: OR_choiceE_def wp: hoare_drop_imps)

crunches handle_interrupt
for cur_thread[wp]: "\<lambda>s::det_state. P (cur_thread s)"
  (wp: hoare_drop_imp crunch_wps simp: crunch_simps)

crunches handle_reserved_irq
  for release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and valid_release_q[wp]: "\<lambda>s. valid_release_q s"

crunches install_tcb_cap
  for ct_not_in_release_q[wp]: "ct_not_in_release_q :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps preemption_point_inv ignore: check_cap_at simp: check_cap_at_def)

lemma cap_revoke_ct_not_in_release_q[wp]:
  "cap_revoke slot \<lbrace>ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: cap_revoke_preservation2 preemption_point_inv)

lemma invoke_cnode_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_cnode iv
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_splits [split del]
  by (wpsimp simp: invoke_cnode_def)+

lemma invoke_tcb_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_tcb iv
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q:: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
           prefer 8
           apply (case_tac x82; wpsimp)
          apply (wpsimp simp: install_tcb_frame_cap_def | wpsimp wp: hoare_drop_imps)+
  done

lemma invoke_irq_control_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   invoke_irq_control iv
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (case_tac iv; wpsimp)

lemma perform_invocation_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q \<rbrace>
   perform_invocation block call can_donate iv
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q  :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac iv; simp)
        apply (wpsimp wp: invoke_cnode_ct_not_in_release_qE_E
                          invoke_irq_control_ct_not_in_release_qE_E)+
  done

lemma handle_invocation_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def syscall_def
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wpsimp wp: syscall_valid hoare_drop_imps set_thread_state_ct_in_state
                    perform_invocation_ct_not_in_release_qE_E[simplified pred_conj_def conj_assoc])
  done

lemma handle_event_ct_not_in_release_qE_E[wp]:
  "\<lbrace>ct_not_in_release_q\<rbrace>
   handle_event e
   -, \<lbrace>\<lambda>rv. ct_not_in_release_q :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       apply (rename_tac syscall)
       apply (case_tac syscall; simp)
                 apply (wpsimp simp: handle_send_def handle_call_def
                                 wp: handle_invocation_ct_not_in_release_qE_E
                                     check_budget_restart_true)+
  done

lemma check_budget_restart_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>rv. scheduler_act_sane \<rbrace>"
  unfolding check_budget_restart_def
  by wpsimp

lemma check_budget_restart_simple_sched_action_sane[wp]:
  "\<lbrace>simple_sched_action :: 'state_ext state \<Rightarrow> _\<rbrace>
   check_budget_restart
   \<lbrace>\<lambda>rv. simple_sched_action \<rbrace>"
  unfolding check_budget_restart_def
  by wpsimp

crunches reply_from_kernel
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s) (cur_thread s)"

lemma handle_fault_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   handle_fault thread x1
   \<lbrace>\<lambda>rv. scheduler_act_sane:: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_fault_def handle_no_fault_def send_fault_ipc_def
  by (wpsimp wp: thread_set_ct_in_state)

crunches complete_signal, do_nbrecv_failed_transfer
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s) (cur_thread s)"
  (wp: crunch_wps ignore: possible_switch_to)

crunches schedule_tcb, maybe_return_sc
  for scheduler_action[wp]: "scheduler_act_sane"
  (wp: crunch_wps simp: crunch_simps)

lemma receive_ipc_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   receive_ipc thread cap is_blocking reply_cap
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: receive_ipc_def wp: hoare_drop_imp possible_switch_to_scheduler_act_sane' gts_wp)
            apply (rule_tac Q="\<lambda>_. scheduler_act_sane and ct_not_blocked" in hoare_strengthen_post[rotated])
             apply (clarsimp simp: ct_in_state_def tcb_at_kh_simps vs_all_heap_simps)
            apply (wpsimp simp: send_ipc_def wp: hoare_drop_imp hoare_vcg_all_lift get_sk_obj_ref_wp)+
  done

lemma receive_signal_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   receive_signal thread cap is_blocking
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: receive_signal_def wp: hoare_drop_imp gts_wp)

lemma handle_recv_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   handle_recv is_blocking can_reply
   \<lbrace>\<lambda>rv. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding handle_recv_def
  by (wpsimp wp: thread_set_ct_in_state hoare_drop_imp hoare_vcg_all_lift
           simp: Let_def lookup_cap_def)

lemma handle_timeout_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   handle_timeout tptr ex
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def send_fault_ipc_def
  by (wpsimp wp: thread_set_ct_in_state)

lemma handle_fault_reply_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_blocked\<rbrace>
   handle_fault_reply cap thread label msg
   \<lbrace>\<lambda>_. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (case_tac cap; wpsimp)

lemma cap_cap_slot_fold:
  "(\<forall>cap ref cnodeindex. x = (cap, ref, cnodeindex) \<longrightarrow> P cap ref cnodeindex) = P (fst x) (fst (snd x)) (snd (snd x))"
  by (metis fst_conv snd_conv surj_pair)

lemma handle_invocation_schact_sane:
  "\<lbrace>simple_sched_action and ct_in_state active and invs\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>rv. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def
  supply if_split [split del]
  apply (wpsimp wp: syscall_valid)
         apply (wpsimp wp: hoare_drop_imp, clarsimp cong: conj_cong)
        apply (wpsimp wp: perform_invocation_scheduler_act_sane, clarsimp cong: conj_cong)
       apply (wpsimp wp: ct_in_state_set)
      apply wpsimp
     apply (wpsimp wp: hoare_drop_imps simp: cap_cap_slot_fold)
    apply wpsimp
   apply wpsimp
  apply (clarsimp cong: conj_cong split: if_splits)
  by (fastforce simp: ct_in_state_def
                elim: st_tcb_at_strengthen_pred
               intro: runnable_nonz_cap_to fault_tcbs_valid_states_active)

(* FIXME: RT move to Invariants_AI *)
lemma ct_active_fault_tcb_at_None:
  "ct_active s \<Longrightarrow> fault_tcbs_valid_states s \<Longrightarrow> fault_tcb_at ((=) None) (cur_thread s) s"
  apply (erule fault_tcbs_valid_states_active)
  apply (clarsimp simp: fault_tcbs_valid_states_def ct_in_state_def)
  done

lemma update_waiting_ntfn_ct_in_state[wp]:
  "\<lbrace>ct_in_state P and (\<lambda>s. queue \<noteq> [] \<longrightarrow> cur_thread s = hd queue \<longrightarrow> P Running)\<rbrace>
     update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  by (wpsimp wp: sts_ctis_neq hoare_drop_imps)

lemma install_tcb_frame_cap_ct_not_blocked[wp]:
  "\<lbrace>ct_not_blocked\<rbrace>
   install_tcb_frame_cap target slot buffer
   \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding install_tcb_frame_cap_def
  by (wpsimp wp: check_cap_inv hoare_drop_imp thread_set_ct_in_state)

lemma bind_notification_ct_not_blocked[wp]:
  "\<lbrace>ct_in_state P\<rbrace>
   bind_notification tcbptr ntfnptr
   \<lbrace>\<lambda>rv. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding bind_notification_def
  by (wpsimp wp: set_tcb_obj_ref_ct_in_state)

lemma test_possible_switch_to_ct_not_blocked[wp]:
  "\<lbrace>ct_in_state P\<rbrace>
   test_possible_switch_to thread
   \<lbrace>\<lambda>rv. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding test_possible_switch_to_def
  by (wpsimp wp: set_tcb_obj_ref_ct_in_state)

lemma restart_ct_not_blocked[wp]:
  "\<lbrace>ct_in_state P and (\<lambda>s. thread = cur_thread s \<longrightarrow> (P Restart \<and> P Inactive))\<rbrace>
   restart thread
   \<lbrace>\<lambda>rv. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding restart_def
  apply (wpsimp wp: hoare_vcg_imp_lift' sts_ctis_neq cancel_ipc_ct_in_state get_tcb_obj_ref_wp gts_wp)
  done

crunches maybe_sched_context_unbind_tcb, maybe_sched_context_bind_tcb
  for ct_not_blocked[wp]: "ct_not_blocked :: 'state_ext state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps set_tcb_obj_ref_ct_in_state)

crunches set_priority
  for ct_not_blocked[wp]: "ct_not_blocked :: 'state_ext state \<Rightarrow> _"
  (ignore: set_object simp: crunch_simps wp: crunch_wps thread_set_ct_in_state)

lemma invoke_tcb_ct_not_blocked[wp]:
  "\<lbrace>ct_not_blocked\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  apply (case_tac iv; simp)
          prefer 8
          apply (rename_tac tptr epptr_opt)
          apply (case_tac epptr_opt; simp)
           apply (wpsimp wp: mapM_x_wp_inv hoare_drop_imp)+
  done

lemma invoke_untyped_ct_not_blocked[wp]:
  "\<lbrace>invs and ct_active and valid_untyped_inv iv\<rbrace>
   invoke_untyped iv
   -, \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding invoke_untyped_def
  apply wpsimp
  apply (clarsimp simp: ct_in_state_def)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply fastforce
  apply (drule ex_nonz_cap_to_overlap,
         ((simp add: cte_wp_at_caps_of_state descendants_range_def2
                     empty_descendants_range_in)+))
  apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)
  apply (case_tac "tcb_state y"; simp)
  done

lemma cap_revoke_ct_not_blocked[wp]:
  "\<lbrace>ct_not_blocked\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  by (wpsimp wp: cap_revoke_preservation)

lemma invoke_cnode_ct_not_blocked[wp]:
  "\<lbrace>ct_not_blocked\<rbrace>
   invoke_cnode iv
   -, \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  supply if_split [split del]
  unfolding invoke_cnode_def
  by wpsimp

lemma perform_invocation_ct_not_blocked[wp]:
  "\<lbrace>invs and ct_active and valid_invocation iv\<rbrace>
   perform_invocation block call can_donate iv
   -, \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (case_tac iv; wpsimp)

lemma handle_invocation_ct_not_blocked[wp]:
  "\<lbrace>ct_active and invs\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   -, \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_invocation_def
  supply if_split [split del]
  apply (wpsimp wp: syscall_valid)
               apply (wpsimp wp: set_thread_state_ct_in_state)
              apply wpsimp
         apply (wpsimp)
   apply (rule_tac Q'="\<lambda>r s.
                  thread = cur_thread s \<and>
                  ct_active s \<and>
                  s \<turnstile> (fst r) \<and>
                  invs s \<and>
                  cte_wp_at ((=) (fst r)) (snd r) s \<and>
                  ex_cte_cap_wp_to (\<lambda>_. True) (snd r) s \<and>
                  real_cte_at (snd r) s \<and>
                  (\<forall>r\<in>zobj_refs (fst r). ex_nonz_cap_to r s) \<and> invs s" in hoare_post_imp_R[rotated])
      apply (clarsimp simp: ct_in_state_def cong: conj_cong)
      apply (strengthen runnable_nonz_cap_to ct_active_fault_tcb_at_None)
      apply (clarsimp simp: ct_in_state_def runnable_eq_active, fastforce)
      apply wpsimp+
  done

lemma handle_event_ct_not_blockedE_E[wp]:
  "\<lbrace>ct_in_state activatable and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and invs\<rbrace>
   handle_event e
   -, \<lbrace>\<lambda>rv. ct_not_blocked :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       subgoal for syscall
       apply (case_tac syscall; simp)
                  apply (wpsimp simp: handle_call_def handle_send_def wp: check_budget_restart_true
                         | erule active_from_running)+
       done
       apply (wpsimp)+
  done

lemma handle_yield_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace>
   handle_yield
   \<lbrace>\<lambda>rv. scheduler_act_sane :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding handle_yield_def
  by wpsimp

lemma check_budget_restart_if_lift:
  "\<lbrace>R\<rbrace> check_budget_restart \<lbrace>\<lambda>_. Q\<rbrace>
   \<Longrightarrow> \<lbrace>P and R\<rbrace> check_budget_restart \<lbrace>\<lambda>r. if r then P else Q\<rbrace>"
  apply (wpsimp wp: hoare_vcg_if_lift2 check_budget_restart_true)
                 apply (wpsimp wp: hoare_drop_imp, simp)
  done

lemma check_budget_ct_not_BlockedOnReceive[wp]:
  "check_budget \<lbrace>ct_in_state not_BlockedOnReceive :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: check_budget_ct_in_state; simp add: is_BlockedOnReceive_def)

lemma charge_budget_ct_not_BlockedOnReceive[wp]:
  "charge_budget consumed canTimeout \<lbrace>ct_in_state not_BlockedOnReceive :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: charge_budget_ct_in_state; simp add: is_BlockedOnReceive_def)

lemmas check_budget_restart_false = hoare_drop_imp[where f=check_budget_restart and R="\<lambda>r s. \<not>r"]

lemma ct_active_sc_cur_sc_active:
  "active_sc_tcb_at (cur_thread s) s \<Longrightarrow> bound_sc_tcb_at (\<lambda>p. p = Some (cur_sc s)) (cur_thread s) s \<Longrightarrow> cur_sc_active s"
  by (clarsimp simp: active_sc_tcb_at_def2 is_sc_active_kh_simp tcb_at_kh_simps vs_all_heap_simps)

lemma cur_sc_active_ct_active_sc:
  "cur_sc_active s \<Longrightarrow> bound_sc_tcb_at (\<lambda>p. p = Some (cur_sc s)) (cur_thread s) s \<Longrightarrow> active_sc_tcb_at (cur_thread s) s"
  by (fastforce simp: active_sc_tcb_at_def2 is_sc_active_kh_simp)

lemmas schat_is_rct_ct_active_sc = invs_cur_sc_tcb_symref[THEN cur_sc_active_ct_active_sc[rotated]]

end

context DetSchedSchedule_AI_handle_hypervisor_fault_det_ext begin

lemma handle_interrupt_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_not_BlockedOnNtfn and ct_in_state not_BlockedOnReceive and invs\<rbrace>
   handle_interrupt irq
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  by (wpsimp wp: hoare_drop_imp send_signal_scheduler_act_sane hoare_vcg_if_lift2)

lemma handle_event_scheduler_act_sane:
  "\<lbrace>schact_is_rct
    and invs
    and ct_in_state activatable
    and cur_sc_active
    and ct_not_in_release_q
    and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac e; simp)
       apply (rename_tac syscall)
  subgoal for syscall
    apply (case_tac syscall; simp)
              apply (wpsimp simp: handle_call_def handle_send_def
                              wp: handle_invocation_schact_sane check_budget_restart_true check_budget_restart_false)
              apply (fastforce elim: active_from_running)
             apply ((wpsimp simp: handle_call_def handle_send_def
                             wp: handle_invocation_schact_sane check_budget_restart_true
                                 check_budget_restart_false
                    | strengthen ct_runnable_ct_not_blocked active_from_running)+)[1]
             apply (clarsimp simp: is_schedulable_bool_def2 )
             apply (strengthen schat_is_rct_ct_active_sc)
             apply (clarsimp simp: schact_is_rct_def ct_in_state_def2[symmetric] runnable_eq_active)
             apply (fastforce elim: active_from_running)
            apply ((wpsimp simp: handle_call_def handle_send_def
                            wp: handle_invocation_schact_sane check_budget_restart_true
                                check_budget_restart_false
                   | strengthen ct_runnable_ct_not_blocked active_from_running)+)[1]
            apply (clarsimp simp: is_schedulable_bool_def2 )
            apply (strengthen schat_is_rct_ct_active_sc)
            apply (clarsimp simp: schact_is_rct_def ct_in_state_def2[symmetric] runnable_eq_active)
            apply (fastforce elim: active_from_running)
           apply ((wpsimp simp: handle_call_def handle_send_def
                           wp: handle_invocation_schact_sane check_budget_restart_true
                               check_budget_restart_false
                  | strengthen ct_runnable_ct_not_blocked active_from_running)+)[1]
           apply (clarsimp simp: is_schedulable_bool_def2 )
           apply (strengthen schat_is_rct_ct_active_sc)
           apply (clarsimp simp: schact_is_rct_def ct_in_state_def2[symmetric] runnable_eq_active)
           apply (fastforce elim: active_from_running)
          apply ((wpsimp simp: handle_call_def handle_send_def
                          wp: handle_invocation_schact_sane check_budget_restart_true
                              check_budget_restart_false
                 | strengthen ct_runnable_ct_not_blocked active_from_running)+)[1]
          apply fastforce
         apply ((wpsimp simp: handle_call_def handle_send_def
                         wp: handle_invocation_schact_sane check_budget_restart_true
                             check_budget_restart_false
                | strengthen ct_runnable_ct_not_blocked active_from_running)+)[1]
         apply fastforce
        apply (wpsimp simp: handle_call_def handle_send_def
                        wp: handle_invocation_schact_sane check_budget_restart_true
                            check_budget_restart_false
               | strengthen ct_runnable_ct_not_blocked active_from_running)+
    done
      apply (wpsimp wp: check_budget_restart_if_lift, fastforce)
     apply (wpsimp wp: check_budget_restart_if_lift, fastforce)
    apply (wpsimp wp: hoare_drop_imp, fastforce)
   apply (wpsimp wp: check_budget_restart_if_lift, fastforce)
  apply (wpsimp, fastforce)
  done

lemma call_kernel_valid_sched:
  "\<lbrace>\<lambda>s. invs s \<and> valid_sched s \<and> (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) s \<and> ct_in_state activatable s
        \<and> scheduler_action s = resume_cur_thread
        \<and> is_schedulable_bool (cur_thread s) (in_release_queue (cur_thread s) s) s
        \<and> bound_sc_tcb_at bound (cur_thread s) s \<and> valid_refills (cur_sc s) s
        \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> ct_released s\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: call_kernel_def) (*

  apply (wp schedule_valid_sched activate_thread_valid_sched | simp)+
(*
apply (wp|wpc)+
apply (rule activate_thread_valid_sched)
apply (rule schedule_valid_sched)

apply (rule validE_valid)
apply (rule handleE_wp)
apply (rule_tac Q="\<lambda>_.  ct_active and ct_not_in_release_q and
               (\<lambda>s. budget_ready (cur_thread s) s) and
               (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
               (\<lambda>s. budget_sufficient (cur_thread s) s) and
               (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and
               (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s) and
               valid_sched and
               scheduler_act_sane and
               ct_not_queued and
               cur_sc_in_release_q_imp_zero_consumed and
               (\<lambda>s. cur_sc_offset_ready (consumed_time s) s) and
               (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s) and
               cur_sc_budget_sufficient and
               invs"
and E="\<lambda>_.  ct_active and ct_not_in_release_q and
               (\<lambda>s. budget_ready (cur_thread s) s) and
               (\<lambda>s. \<forall>t. in_release_q t s \<longrightarrow> budget_sufficient t s) and
               (\<lambda>s. budget_sufficient (cur_thread s) s) and
               (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and
               (\<lambda>s. \<not> sc_is_round_robin (cur_sc s) s) and
               valid_sched and
               scheduler_act_sane and
               ct_not_queued and
               cur_sc_in_release_q_imp_zero_consumed and
               (\<lambda>s. cur_sc_offset_ready (consumed_time s) s) and
               (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s) and
               cur_sc_budget_sufficient and
               invs" in hoare_post_impErr[rotated])
apply ((clarsimp simp: valid_sched_def invs_def is_schedulable_bool_def valid_state_def
split: option.split)+)[2]


apply (wp hoare_vcg_conj_lift hoare_drop_imp|wpc)+
apply wps



apply (wp hoare_vcg_conj_lift hoare_drop_imp|wpc|wps)+





apply (wp_once handleE_wp)

apply wp_trace

apply (wpsimp wp: handle_interrupt_valid_sched)


  apply (wp schedule_valid_sched activate_thread_valid_sched handle_interrupt_valid_sched | simp)+ *)
           apply (erule invs_valid_idle)
          apply wp
         apply (wp is_schedulable_wp)
          apply (wp call_kernel_check_budget_helper)
         apply (wp call_kernel_valid_sched_charge_budget_helper)
        apply (wp is_schedulable_wp)+
(*
     apply (rule_tac Q="\<lambda>_. valid_sched and invs and ct_not_in_release_q and ct_not_queued
                            and (\<lambda>s. valid_refills (cur_sc s) s)
                            and scheduler_act_sane and cur_sc_chargeable" in hoare_strengthen_post)
      apply (wpsimp wp: scheduler_act_sane_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
     apply (clarsimp simp: invs_def)
*)
     apply (rule_tac Q="\<lambda>_. valid_sched and invs and ct_not_in_release_q and ct_not_queued
                            and schact_is_rct and ct_released and (\<lambda>s. valid_refills (cur_sc s) (- 1) s)" in hoare_strengthen_post)
      apply wpsimp
     apply (auto simp: schact_is_rct_def)[1]
(*
  apply (wpsimp wp: schedule_valid_sched activate_thread_valid_sched
  hoare_vcg_ball_lift
               simp: valid_sched_valid_release_q)
      apply (rule_tac Q="\<lambda>rv. invs" in hoare_strengthen_post)
       apply wp
      apply (erule invs_valid_idle)
     apply (wp call_kernel_valid_sched_check_budget_helper)
*)
    apply (rule hoare_strengthen_post
      [where Q="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> valid_sched s \<and> invs s
                        \<and> ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) s
                        \<and> scheduler_act_sane s \<and> (cur_sc_chargeable s)"])
     apply (wpsimp wp: getActiveIRQ_neq_non_kernel)
     apply (clarsimp simp: cur_sc_chargeable_def)
    apply fastforce
   apply (rule_tac Q="\<lambda>rv s. valid_sched s \<and> invs s" and
(*
                   E="\<lambda>rv s. (ct_not_in_release_q s \<and>
                              ct_not_queued s \<and> scheduler_act_sane s \<and> cur_sc_chargeable s \<and>
                              valid_refills (cur_sc s) s) \<and> (valid_sched s \<and> invs s)"
           in hoare_post_impErr)
*)
(*
                   E="\<lambda>rv s. (ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) (- 1) s \<and>
                              schact_is_rct s \<and> ct_released s) \<and>
                             valid_sched s \<and> invs s" in hoare_post_impErr)
      E="\<lambda>rv s. (ct_not_in_release_q s \<and> ct_not_queued s \<and> valid_refills (cur_sc s) 0 s \<and> schact_is_rct s \<and> ct_released s) \<and> valid_sched s \<and> invs s" in hoare_post_impErr)
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
*)*)
sorry (* call_kernel_valid_sched *)

end

end
