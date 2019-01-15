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

(* FIXME: move *)
lemma valid_blocked_except_set_empty:
  "valid_blocked_except_set {} = valid_blocked"
  by (clarsimp simp: valid_blocked_except_set_def valid_blocked_def)

lemma rt_assumptions:
  "\<not>in_release_queue (cur_thread s) s
                       \<and> sc_tcb_sc_at (\<lambda>sc. sc = Some (cur_thread s)) (cur_sc s) s"

  "\<lbrakk>kheap s rp = Some (Reply reply);
   (\<exists>thread. reply_tcb reply = Some thread \<and> (st_tcb_at ((=) (BlockedOnReply (Some rp))) thread s))\<rbrakk>
  \<Longrightarrow> \<forall>scp. reply_sc reply = Some scp \<longrightarrow> test_sc_refill_max scp s \<and>
        sc_tcb_sc_at (\<lambda>t. \<exists>callee. t = Some callee \<and> st_tcb_at inactive callee s) scp s"

  "st_tcb_at (\<lambda>st. \<exists>rp. st = (BlockedOnReply (Some rp)) \<longrightarrow>
      (\<exists>reply. kheap s rp = Some (Reply reply) \<and>
      (\<forall>scp. reply_sc reply = Some scp \<longrightarrow> test_sc_refill_max scp s \<and>
               sc_tcb_sc_at (\<lambda>t. \<exists>callee. t = Some callee
                 \<and> st_tcb_at inactive callee s) scp s))) thread s"

  "sc_period sc = 0 \<Longrightarrow> length (sc_refills sc) = 2" (* more assumptions? *)
  "\<not> (t \<in> set (ready_queues s d p) \<and> t \<in> set (release_queue s))"
  sorry (* rt_assumptions *)

lemma cur_time_assumption:
  "cur_time s \<le> cur_time s + kernelWCET_ticks"
  sorry (* when time is moved forward, there is no overflow? *)

lemmas ct_assumptions = rt_assumptions(1)
(*
lemmas callee_must_be_inactive_reply = rt_assumptions(2) (* sym_refs assumed *)
lemmas callee_must_be_inactive_tcb = rt_assumptions(3)
lemmas round_robin_refills = rt_assumptions(4)
lemmas ready_or_released = rt_assumptions(5)
*)

(* FIXME move *)
lemma not_in_release_q_simp[dest!]:
   "\<not> in_release_queue t s \<Longrightarrow> not_in_release_q t s"
  by (simp add: in_release_queue_def not_in_release_q_def)

lemma valid_sched_switch_thread_is_schedulable:
  "\<lbrakk>valid_sched s; scheduler_action s = switch_thread thread\<rbrakk> \<Longrightarrow>
     is_schedulable_opt thread (in_release_queue thread s) s = Some True"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
       is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def get_tcb_rev
       in_release_queue_def)

lemma simple_sched_act_not[simp]:
  "simple_sched_action s \<Longrightarrow> scheduler_act_not t s"
  by (clarsimp simp: simple_sched_action_def scheduler_act_not_def)

lemma is_schedulable_sp':
  "\<lbrace>P\<rbrace> is_schedulable tp b \<lbrace>\<lambda>rv. (\<lambda>s. rv = is_schedulable_bool tp b s) and P\<rbrace>"
  apply (clarsimp simp: is_schedulable_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: hoare_vcg_if_lift2 obj_at_def is_tcb wp: get_sched_context_wp)
  apply(rule conjI)
   apply (clarsimp simp: Option.is_none_def is_schedulable_bool_def get_tcb_def)
  by (clarsimp simp: is_schedulable_bool_def get_tcb_def test_sc_refill_max_def split: option.splits)

lemma set_tcb_queue_wp[wp]:
  "\<lbrace>\<lambda>s. P (ready_queues_update (\<lambda>_ t' p. if t' = t \<and> p = prio then queue else ready_queues s t' p) s)\<rbrace>
       set_tcb_queue t prio queue \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: set_tcb_queue_def)
  apply wp
  done

lemma get_tcb_queue_wp[wp]: "\<lbrace>\<lambda>s. P (ready_queues s t p) s\<rbrace> get_tcb_queue t p \<lbrace>P\<rbrace>"
  apply (simp add: get_tcb_queue_def)
  apply wp
  done

lemma enqueue_distinct[intro!]: "distinct queue \<Longrightarrow> distinct (tcb_sched_enqueue thread queue)"
  apply (simp add: tcb_sched_enqueue_def)
  done

(*
lemma tcb_release_enqueue_wp[wp]:
  "\<lbrace>\<lambda>s. P (release_queue_update (\<lambda>_ t' p. if t' = t then queue else release_queue s t' p) s)\<rbrace>
       tcb_release_enqueue t  \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: tcb_release_enqueue_def)
  apply wp
  done *) (* this is actually rather complicated to state, because the queue is sorted wrt SC *)

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 resume_cur_thread kh rq"
  "weak_valid_sched_action_2 choose_new_thread kh rq"
  by (simp_all add: weak_valid_sched_action_def)

lemma switch_in_cur_domain_trivs[iff]:
  "switch_in_cur_domain_2 resume_cur_thread ekh cdom"
  "switch_in_cur_domain_2 choose_new_thread ekh cdom"
  by (simp_all add: switch_in_cur_domain_def)

lemma ct_in_cur_domain_2_trivs[iff]:
  "ct_in_cur_domain_2 thread thread' (switch_thread t) cdom ekh"
  "ct_in_cur_domain_2 thread thread' choose_new_thread cdom ekh"
  by (simp_all add: ct_in_cur_domain_2_def)

lemma valid_sched_action_triv[iff]:
  "valid_sched_action_2 choose_new_thread kh ct cdom rq"
  by (simp add: valid_sched_action_def)

lemma simple_sched_action_trivs[iff]:
  "simple_sched_action_2 resume_cur_thread"
  "simple_sched_action_2 choose_new_thread"
  by (simp_all add: simple_sched_action_def)

lemma scheduler_act_not_trivs[iff]:
  "scheduler_act_not_2 resume_cur_thread t"
  "scheduler_act_not_2 choose_new_thread t"
  by (simp_all add: scheduler_act_not_def)

lemma ko_at_etcbD:
  "ko_at (TCB tcb) t s \<Longrightarrow> etcbs_of s t = Some (etcb_of tcb)"
  by (simp add: obj_at_def etcbs_of'_def)

lemma etcb_priority_etcb_of[simp]:
  "etcb_priority (etcb_of tcb) = tcb_priority tcb"
  by (simp add: etcb_of_def)

lemma etcb_domain_etcb_of[simp]:
  "etcb_domain (etcb_of tcb) = tcb_domain tcb"
  by (simp add: etcb_of_def)

lemma etcb_of_eq[simp]:
  "(etcb_of t = etcb_of t') = (tcb_priority t = tcb_priority t' \<and> tcb_domain t = tcb_domain t')"
  by (simp add: etcb_of_def)

lemmas thread_get_prio_wp[wp] = thread_get_wp' [where f=tcb_priority]
lemmas thread_get_dom_wp[wp] = thread_get_wp' [where f=tcb_domain]

lemma tcb_sched_action_enqueue_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and active_sc_tcb_at thread
     and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  by (clarsimp simp: valid_ready_qs_def tcb_sched_enqueue_def obj_at_def etcb_defs)

lemma tcb_sched_action_append_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and st_tcb_at runnable thread and active_sc_tcb_at thread
     and budget_sufficient thread and budget_ready thread\<rbrace>
     tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  by (clarsimp simp: valid_ready_qs_def tcb_sched_append_def obj_at_def etcb_defs)

(* this is not safe! *)
lemma tcb_sched_action_dequeue_valid_ready_qs:
  "\<lbrace>valid_ready_qs\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: valid_ready_qs_def2 etcb_at_def tcb_sched_dequeue_def
         split: option.splits)
  apply blast
  done

lemma tcb_sched_action_dequeue_valid_ready_qs':
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
and releaqse_queue[wp]: "\<lambda>s. P (release_queue s)"

lemma tcb_sched_action_enqueue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_enqueue_def not_queued_def
         split: option.splits)
  done

lemma tcb_sched_action_append_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_append_def not_queued_def
                  split: option.splits)
  done

lemma tcb_sched_action_dequeue_ct_not_in_q[wp]:
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

lemma tcb_release_remove_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (wpsimp simp: active_sc_tcb_at_defs tcb_release_remove_def weak_valid_sched_action_def
               tcb_sched_dequeue_def)

lemma tcb_release_remove_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp simp: valid_sched_action_def)

crunch valid_sched_action[wp]: tcb_sched_action valid_sched_action

lemma tcb_sched_action_enqueue_valid_blocked_except:  (* not_in_release_q thread *)
  "\<lbrace>valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>" (* thread was not in ready queue before *)
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_enqueue_def valid_blocked_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_action_enqueue_valid_blocked_except_set_insert:
  "\<lbrace>valid_blocked_except_set S\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_enqueue_def valid_blocked_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_action_enqueue_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  by (wpsimp wp: tcb_sched_action_enqueue_valid_blocked_except_set_insert
           simp: valid_blocked_except_set_empty[symmetric])

lemma tcb_sched_action_append_valid_blocked_except:
  "\<lbrace>valid_blocked_except thread\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_append_def valid_blocked_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_action_append_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: thread_get_def tcb_sched_action_def)
  by (fastforce simp: tcb_sched_append_def valid_blocked_def not_queued_def valid_blocked_except_def
      dest!: get_tcb_SomeD split: option.split_asm)

lemma tcb_sched_action_append_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: thread_get_def tcb_sched_action_def)

lemma tcb_sched_action_enqueue_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: thread_get_def tcb_sched_action_def)

lemma tcb_sched_action_dequeue_valid_blocked_except: (* in_ready_q thread *)
  "\<lbrace>valid_blocked\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  by (fastforce simp: tcb_sched_dequeue_def pred_tcb_at_def valid_blocked_def
                      valid_blocked_except_def not_queued_def obj_at_def)

lemma tcb_sched_action_dequeue_valid_blocked_except2:
  "\<lbrace>valid_blocked_except thread\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  by (fastforce simp: tcb_sched_dequeue_def pred_tcb_at_def valid_blocked_def
                      valid_blocked_except_def not_queued_def obj_at_def)

lemma tcb_sched_action_dequeue_valid_blocked_not_queued:
  "\<lbrace>valid_blocked and not_queued thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def)
  apply (clarsimp simp: valid_blocked_def obj_at_def tcb_sched_dequeue_def not_queued_def
      split: if_splits)
  apply(case_tac "t=thread"; clarsimp)
   apply fastforce
  by (drule_tac x=t in spec, fastforce)

lemma tcb_sched_action_dequeue_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def)

lemma tcb_sched_action_dequeue_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: valid_blocked_def not_queued_def obj_at_def)
  apply (case_tac "t=thread", clarsimp)
   apply (drule_tac x="tcb_domain tcb" in spec)
   apply (drule_tac x="tcb_priority tcb" in spec)
   apply (clarsimp simp: tcb_sched_dequeue_def pred_tcb_at_def obj_at_def)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (clarsimp simp: tcb_sched_dequeue_def pred_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcba"; fastforce)
  done

abbreviation valid_sched_except_blocked_2 where
  "valid_sched_except_blocked_2 queues sa cdom ctime kh ct it rq \<equiv>
    valid_ready_qs_2 queues ctime kh \<and> valid_release_q_2 rq kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_2 sa kh ct cdom rq \<and>
    ct_in_cur_domain_2 ct it sa cdom (etcbs_of' kh) \<and> valid_idle_etcb_2 (etcbs_of' kh)"

abbreviation valid_sched_except_blocked :: "det_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked s \<equiv>
   valid_sched_except_blocked_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s)
                                (cur_thread s) (idle_thread s) (release_queue s)"

declare valid_idle_etcb_lift[wp]


lemma tcb_sched_action_enqueue_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and not_cur_thread thread
    and active_sc_tcb_at thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: tcb_sched_action_enqueue_valid_blocked_except)

lemma tcb_sched_action_append_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and active_sc_tcb_at thread
     and not_cur_thread thread and valid_blocked_except thread
    and budget_ready thread and budget_sufficient thread\<rbrace>
      tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: tcb_sched_action_append_valid_blocked_except)

lemma tcb_sched_action_dequeue_valid_sched_not_runnable:
  "\<lbrace>valid_sched and (\<lambda>s. \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_sched_action_dequeue_valid_blocked tcb_sched_action_dequeue_valid_ready_qs)+

lemma tcb_sched_action_dequeue_valid_sched_not_queued:
  "\<lbrace>valid_sched and not_queued thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def
               wp: tcb_sched_action_dequeue_valid_blocked_not_queued
                   tcb_sched_action_dequeue_valid_ready_qs)

lemma tcb_sched_action_dequeue_valid_sched_except_blocked:
  "\<lbrace>valid_sched\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_sched_action_dequeue_valid_blocked_except tcb_sched_action_dequeue_valid_ready_qs)+

lemma tcb_release_remove_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def valid_blocked_except_def valid_blocked_def
                   tcb_sched_dequeue_def not_in_release_q_def) fastforce

lemma tcb_release_remove_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s))\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  apply (clarsimp simp: valid_blocked_def not_in_release_q_def obj_at_def)
  apply (case_tac "t=thread", clarsimp)
   apply (clarsimp simp: tcb_sched_dequeue_def pred_tcb_at_def obj_at_def)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (clarsimp simp: tcb_sched_dequeue_def pred_tcb_at_def obj_at_def)
  done

lemma tcb_release_remove_valid_blocked_not_queued:
  "\<lbrace>valid_blocked and not_in_release_q thread\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def)
  apply (clarsimp simp: valid_blocked_def obj_at_def tcb_sched_dequeue_def not_in_release_q_def
      split: if_splits)
  apply(case_tac "t=thread"; clarsimp)
   apply fastforce
  by (drule_tac x=t in spec, fastforce)

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

lemma set_scheduler_action_rct_valid_blocked:
  "\<lbrace>valid_blocked and simple_sched_action\<rbrace>
     set_scheduler_action resume_cur_thread  \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def simple_sched_action_def split: scheduler_action.splits | wp set_scheduler_action_wp)+
  done

crunch valid_ntfn_q[wp]: set_scheduler_action valid_ntfn_q

lemma set_scheduler_action_rct_switch_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))\<rbrace>
   set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply clarsimp
  done

lemma set_scheduler_action_rct_valid_sched:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and simple_sched_action\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  unfolding valid_sched_def
  by (wpsimp wp: set_scheduler_action_rct_valid_blocked)

lemma set_scheduler_action_rct_switch_thread_valid_sched:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp set_scheduler_action_rct_switch_thread_valid_blocked | force)+


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

lemma set_scheduler_action_cnt_valid_blocked_weak:
  "\<lbrace>valid_blocked and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread  \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply (simp add: simple_sched_action_def split: scheduler_action.splits)
  done

lemma set_scheduler_action_cnt_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and (\<lambda>s. \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread  \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (simp add: valid_blocked_except_set_def, wp set_scheduler_action_wp)
  apply clarsimp
  apply (erule_tac x=t in allE)
  apply (erule impCE)
   apply force
  apply (erule impCE)
   apply force
  apply (force simp: not_queued_def)
  done

lemmas set_scheduler_action_cnt_valid_blocked = set_scheduler_action_cnt_valid_blocked_except_set
                                                [of "{}", simplified valid_blocked_except_set_empty]

lemma set_scheduler_action_cnt_weak_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def simple_sched_action_def split: scheduler_action.splits | wp set_scheduler_action_cnt_valid_blocked)+

lemma set_scheduler_action_simple_sched_action[wp]:
  "\<lbrace>K $ simple_sched_action_2 action\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (simp add: set_scheduler_action_def | wp)+
crunch simple_sched_action[wp]: tcb_sched_action, update_cdt_list simple_sched_action

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

lemma reschedule_required_valid_ready_qs[wp]:
  "reschedule_required \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: reschedule_required_def is_schedulable_def thread_get_def
                  wp: get_sched_context_wp)
  apply (clarsimp simp: pred_tcb_at_def active_sc_tcb_at_def is_refill_sufficient_def
                        obj_at_def test_sc_refill_max_def is_refill_ready_def
               split: option.splits dest!: get_tcb_SomeD)
  by (fastforce simp: Option.is_none_def)

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

lemma reschedule_required_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace>
     reschedule_required \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> bool\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
    apply ((wpsimp wp: set_scheduler_action_cnt_valid_blocked)+)[2]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac xa; clarsimp)
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked tcb_sched_action_enqueue_valid_blocked)
         apply (simp add: tcb_sched_action_def)
         apply (wpsimp simp: get_tcb_queue_def thread_get_def)+
   apply (clarsimp dest!: get_tcb_SomeD simp: get_tcb_rev)
    apply (clarsimp simp: valid_blocked_def valid_blocked_except_def etcb_at_def split: option.splits)
   apply (clarsimp simp: obj_at_def)
   apply (rename_tac tcb scp sca na)
   apply (rule_tac x="tcb_domain tcb" in exI)
   apply (rule_tac x="tcb_priority tcb" in exI)
   apply (clarsimp simp: tcb_sched_enqueue_def)
  apply (wpsimp simp: set_scheduler_action_def)
  apply (clarsimp simp: is_schedulable_bool_def get_tcb_rev valid_blocked_def active_sc_tcb_at_def
      pred_tcb_at_def obj_at_def in_release_queue_def
      split: option.splits; drule_tac x=t in spec; clarsimp)
   apply (case_tac "x2=t"; clarsimp simp: get_tcb_rev)
  apply (case_tac "x2=t"; clarsimp simp: get_tcb_rev)
  apply (case_tac "tcb_state tcb"; clarsimp simp: not_in_release_q_def)
  done

(*
lemma reschedule_required_valid_sched:
  "\<lbrace>valid_ready_qs and weak_valid_sched_action and valid_blocked and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+
*)
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

lemma reschedule_preserves_valid_shed[wp]:
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
  "\<lbrace>simple_sched_action\<rbrace> reschedule_required  \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (simp add: reschedule_required_def | wp)+

lemma tcb_sched_action_enqueue_not_queued:
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
  apply (wpsimp wp: tcb_sched_action_enqueue_not_queued simp: thread_get_def)
  done

lemma not_in_release_q_sa_update[simp]:
  "not_in_release_q t (s\<lparr>scheduler_action :=sa\<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

lemma not_in_release_q_rdq_update[simp]:
  "not_in_release_q t (s\<lparr>ready_queues :=rdq\<rparr>) = not_in_release_q t s"
  by (clarsimp simp: not_in_release_q_def)

crunches reschedule_required
for ct[wp]: "\<lambda>s. P (cur_thread s)"
and not_in_release_q[wp]: "\<lambda>s. P (not_in_release_q t s)"
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

crunches set_tcb_obj_ref,tcb_release_remove
for scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: set_scheduler_action_wp crunch_wps)

lemma tcb_release_remove_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def valid_release_q_def tcb_sched_dequeue_def)

crunches reschedule_required,test_reschedule
for valid_release_q[wp]: valid_release_q
  (wp: set_scheduler_action_wp crunch_wps)


(* misc *)

lemma get_tcb_st_tcb_at:
  "get_tcb t s = Some y \<Longrightarrow> st_tcb_at \<top> t s"
  apply (simp add: get_tcb_def pred_tcb_at_def obj_at_def
              split: option.splits kernel_object.splits)
  done

lemma obj_at_kh_if_split:
  "obj_at_kh P ptr (\<lambda>t. if t = ref then x else kh t)
     = (if ptr = ref then (\<exists>ko. x = (Some ko) \<and> P ko)
        else obj_at_kh P ptr kh)"
  by (fastforce simp: obj_at_kh_def obj_at_def)

lemma st_tcb_at_kh_if_split:
  "st_tcb_at_kh P ptr (\<lambda>t. if t = ref then x else kh t)
     = (if ptr = ref then (\<exists>tcb. x = Some (TCB tcb) \<and> P (tcb_state tcb))
        else st_tcb_at_kh P ptr kh)"
  by (fastforce simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def)

lemma bound_sc_tcb_at_kh_if_split:
  "bound_sc_tcb_at_kh P ptr (\<lambda>t. if t = ref then x else kh t)
     = (if ptr = ref then (\<exists>tcb. x = Some (TCB tcb) \<and> P (tcb_sched_context tcb))
        else bound_sc_tcb_at_kh P ptr kh)"
  by (fastforce simp: bound_sc_tcb_at_kh_def obj_at_kh_def obj_at_def)

lemma test_sc_refill_max_kh_if_split:
  "test_sc_refill_max_kh ptr (\<lambda>p. if p = ref then x else kh p)
     = (if ptr = ref then (\<exists>sc n. x = Some (SchedContext sc n) \<and> (sc_refill_max sc > 0))
        else test_sc_refill_max_kh ptr kh)"
  by (clarsimp simp: test_sc_refill_max_kh_def split: option.splits)
     (rename_tac ko; case_tac ko; clarsimp)

lemma refill_ready_kh_if_split:
  "refill_ready_kh curtime ptr (\<lambda>p. if p = ref then x else kh p)
     = (if ptr = ref then (\<exists>sc n. x = Some (SchedContext sc n)
              \<and> (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks)
        else refill_ready_kh curtime ptr kh)"
  by (clarsimp simp: refill_ready_kh_def split: option.splits)
     (rename_tac ko; case_tac ko; clarsimp)

lemma refill_sufficient_kh_if_split:
  "refill_sufficient_kh ptr (\<lambda>p. if p = ref then x else kh p)
     = (if ptr = ref then (\<exists>sc n. x = Some (SchedContext sc n)
              \<and> (sufficient_refills 0 (sc_refills sc)))
        else refill_sufficient_kh ptr kh)"
  by (clarsimp simp: refill_sufficient_kh_def split: option.splits)
     (rename_tac ko; case_tac ko; clarsimp)

lemma active_sc_tcb_at_kh_if_split:
  "active_sc_tcb_at_kh ptr (\<lambda>t. if t = ref then x else kh t)
     = (\<exists>tcb. (if ptr = ref then x else kh ptr) = Some (TCB tcb)
                 \<and> (\<exists>scp. tcb_sched_context tcb = Some scp
                     \<and> test_sc_refill_max_kh scp (\<lambda>t. if t = ref then x else kh t)))"
  by (fastforce simp: active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_if_split obj_at_kh_def
                      bound_sc_tcb_at_kh_def test_sc_refill_max_kh_if_split)

lemma active_sc_tcb_at_kh_if_split':
  "active_sc_tcb_at_kh ptr (\<lambda>t. if t = ref then x else kh t)
    = bound_sc_tcb_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp
                     \<and> test_sc_refill_max_kh scp (\<lambda>t. if t = ref then x else kh t))
                                                             ptr (\<lambda>t. if t = ref then x else kh t)"
  by (fastforce simp: active_sc_tcb_at_kh_def bound_sc_tcb_at_kh_if_split obj_at_kh_def
                      bound_sc_tcb_at_kh_def test_sc_refill_max_kh_if_split)

lemma budget_ready_kh_if_split:
  "budget_ready_kh curtime ptr (\<lambda>t. if t = ref then x else kh t)
     = (\<exists>tcb. (if ptr = ref then x else kh ptr) = Some (TCB tcb)
                 \<and> (\<exists>scp. tcb_sched_context tcb = Some scp
                      \<and> refill_ready_kh curtime scp (\<lambda>t. if t = ref then x else kh t)))"
  by (fastforce simp: bound_sc_tcb_at_kh_if_split obj_at_kh_def
                      bound_sc_tcb_at_kh_def refill_ready_kh_if_split)

lemma budget_sufficient_kh_if_split:
  "budget_sufficient_kh ptr (\<lambda>t. if t = ref then x else kh t)
     = (\<exists>tcb. (if ptr = ref then x else kh ptr) = Some (TCB tcb)
                 \<and> (\<exists>scp. tcb_sched_context tcb = Some scp
                      \<and> refill_sufficient_kh scp (\<lambda>t. if t = ref then x else kh t)))"
  by (fastforce simp: bound_sc_tcb_at_kh_if_split obj_at_kh_def
                      bound_sc_tcb_at_kh_def refill_sufficient_kh_if_split)

lemma valid_blocked_valid_blocked_except[simp]:
  "valid_blocked s \<Longrightarrow> valid_blocked_except t s"
  by (simp add: valid_blocked_def valid_blocked_except_def)

lemma valid_blocked_valid_blocked_except_set[simp]:
  "valid_blocked s \<Longrightarrow> valid_blocked_except_set S s"
  by (simp add: valid_blocked_def valid_blocked_except_def)

(* set thread_state *)

crunches schedule_tcb,set_thread_state_act
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> bool"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> bool"
  (simp: unless_def is_schedulable_def wp: get_sched_context_wp hoare_vcg_if_lift2)

lemma etcbs_of_update_unrelated:
  "\<lbrakk> kh ref = Some (TCB tcb); etcb_of tcb = etcb_of tcb' \<rbrakk> \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB tcb') else kh r) = etcbs_of' kh"
  by (auto simp: etcbs_of'_def)

lemma etcbs_of_update_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_state_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

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
  "\<lbrace>valid_release_q and K (runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> bool\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: get_sched_context_wp hoare_drop_imp
              simp: is_schedulable_def set_object_def)
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
                   split: option.splits dest!: get_tcb_SomeD)

lemma set_thread_state_not_queued_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (wp | simp add:  set_object_def)+
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split not_in_release_q_def active_sc_tcb_at_defs
                 etcb_defs dest!: get_tcb_SomeD split: option.splits)

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
  apply (clarsimp simp: active_sc_tcb_at_defs)
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
  by (fastforce simp: active_sc_tcb_at_defs split: option.splits)

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
  "\<lbrace>valid_sched_except_blocked and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_thread_state_runnable_valid_ready_qs set_thread_state_runnable_valid_release_q
                    set_thread_state_runnable_valid_sched_action simp: valid_sched_def)
  done

lemma set_thread_state_act_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace>
      set_thread_state_act ref \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_thread_state_act_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_pre)
  apply (rule hoare_when_wp)
   apply (rule hoare_strengthen_post)
    apply (rule set_scheduler_action_cnt_valid_blocked_weak, simp)
  apply clarsimp
  done

lemma set_thread_state_not_blocked_valid_blocked:
  "\<lbrace>valid_blocked and
    (\<lambda>s. \<not> (not_queued ref s \<and> not_in_release_q ref s \<and> scheduler_act_not ref s \<and> ref \<noteq> cur_thread s))\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: gets_wp set_thread_state_act_valid_blocked)
  by (fastforce simp: valid_blocked_def st_tcb_at_kh_def active_sc_tcb_at_defs scheduler_act_not_def
                   dest!: get_tcb_SomeD split: option.splits)

lemma set_thread_state_not_runnable_valid_blocked:
  "\<lbrace>valid_blocked and K (\<not> runnable ts)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: gets_wp set_thread_state_act_valid_blocked)
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_def active_sc_tcb_at_defs
 dest!: get_tcb_SomeD split: option.splits)
  by  (intro conjI impI; clarsimp; fastforce)

lemma set_thread_state_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked_except ref::det_state \<Rightarrow> bool\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wp gts_wp is_schedulable_wp)+
  apply (fastforce simp: valid_blocked_def valid_blocked_except_def st_tcb_at_kh_def st_tcb_at_def
                      active_sc_tcb_at_defs dest!: get_tcb_SomeD)+
  done

lemma set_thread_state_runnable_valid_blocked:  (* ref should be queued *)
  "\<lbrace>valid_blocked and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts
  \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def dest!: get_tcb_SomeD)
  apply (drule_tac x=t in spec, clarsimp simp: get_tcb_rev active_sc_tcb_at_defs st_tcb_at_kh_if_split
      split: option.splits if_splits)
  apply (case_tac "tcb_state y"; clarsimp)
  done

lemma set_thread_state_ready_queues[wp]:
  "\<lbrace>\<lambda>s :: det_state. P (ready_queues s)\<rbrace>
    set_thread_state thread ts
   \<lbrace>\<lambda>r s. P (ready_queues s)\<rbrace>"
  apply (simp add: set_thread_state_def )
  apply (simp add: set_thread_state_act_def[abs_def] reschedule_required_def
                   set_scheduler_action_def set_object_def)
  apply (wp | wpc | simp add: tcb_sched_action_def)+
  done

lemma runnable_eq_active: "runnable = active"
  apply (rule ext)
  apply (case_tac st, simp_all)
  done

crunches set_thread_state
for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: set_object_wp ignore: set_object)

crunches set_thread_state_act
for is_refill_sufficient[wp]: "is_refill_sufficient scp u"
and is_refill_ready[wp]: "is_refill_ready scp"
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
  "\<lbrace>is_refill_ready t\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. is_refill_ready t\<rbrace>"
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
(*
lemma set_thread_state_valid_sched:
  "\<lbrace>valid_sched
    and ((\<lambda>s. not_queued ref s \<and> not_in_release_q ref s \<and> scheduler_act_not ref s \<and> ref \<noteq> cur_thread s
               \<longrightarrow> \<not> runnable ts)
    or (\<lambda>s. in_ready_q ref s \<or> in_release_q ref s \<longrightarrow> runnable ts))\<rbrace>
               set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched::det_state\<Rightarrow>_\<rbrace>"
  apply (rule_tac Q="\<lambda>_ s. valid_sched s \<or> valid_sched s" in hoare_strengthen_post)
  apply (rule hoare_pre)
  apply (rule hoare_vcg_disj_lift)
  apply (wpsimp wp: set_thread_state_not_queued_valid_ready_qs set_thread_state_not_queued_valid_release_q
                    set_thread_state_act_not_valid_sched_action
                    set_thread_state_not_runnable_valid_blocked
               simp: valid_sched_def)


  apply (wpsimp wp: set_thread_state_runnable_valid_ready_qs set_thread_state_runnable_valid_release_q
                     set_thread_state_not_blocked_valid_blocked  set_thread_state_runnable_valid_sched_action
               simp: valid_sched_def)
apply (case_tac "not_queued ref s"; case_tac "not_in_release_q ref s"; clarsimp)
apply (clarsimp simp: valid_sched_def cong: conj_cong)
apply (elim disjE; clarsimp)

apply blast
  done*)

lemma set_thread_state_active_valid_sched:
  "active st \<Longrightarrow>
   \<lbrace>valid_sched and ct_active and (\<lambda>s::det_state. cur_thread s = ct) and active_sc_tcb_at ct\<rbrace>
     set_thread_state ct st \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_ready_qs_def)
  apply (wp hoare_vcg_all_lift)
    apply (rule hoare_lift_Pf [where f="\<lambda>s. ready_queues s", OF _ set_thread_state_ready_queues])
    apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_cases simp: runnable_eq_active)
   apply (wp set_thread_state_runnable_valid_release_q
             set_thread_state_runnable_valid_sched_action set_thread_state_runnable_valid_blocked)
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


lemma st_tcb_at_not:
  "st_tcb_at (\<lambda>st. \<not> P st) t s = (\<not> st_tcb_at P t s \<and> tcb_at t s)"
  apply (clarsimp simp: not_pred_tcb)
  apply (fastforce simp: st_tcb_at_tcb_at)
  done

lemma set_thread_state_not_runnable_valid_ready_qs:
  "\<lbrace>valid_ready_qs and ct_not_in_q and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
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
  "\<lbrace>valid_release_q and ct_not_in_q and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add:  set_object_def | wp)+
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split ct_not_in_q_def etcb_at_def
                        st_tcb_at_not active_sc_tcb_at_defs is_etcb_at'_def etcbs_of'_def
                  split: option.splits dest!: get_tcb_SomeD)

lemma schedule_tcb_ext_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace>
      schedule_tcb ref \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: schedule_tcb_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_pre)
  apply (rule hoare_when_wp)
   apply (wpsimp wp: reschedule_required_valid_blocked)
  apply clarsimp
  done

lemma set_thread_state_sipmle_valid_sched_action:
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
                   set_thread_state_not_runnable_valid_blocked
                   set_thread_state_not_runnable_valid_release_q
               simp: valid_sched_def)

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
  apply (clarsimp simp: tcb_sched_dequeue_def valid_release_q_except_set_def valid_release_q_2_def)
  apply (case_tac "t = thread"; clarsimp simp: Ball_def)
  apply (erule_tac x=t in allE; clarsimp)
  apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def active_sc_tcb_at_kh_def
                        bound_sc_tcb_at_kh_def test_sc_refill_max_kh_def st_tcb_at_def
                        obj_at_def active_sc_tcb_at_def pred_tcb_at_def test_sc_refill_max_def
                  split: option.splits
                  dest!: get_tcb_SomeD)
  apply (subgoal_tac "scp \<noteq> thread"; fastforce)
  done

lemma tcb_release_remove_valid_release_q_except:
  "\<lbrace>valid_release_q_except thread\<rbrace>
      tcb_release_remove thread
   \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding tcb_release_remove_def
  by (wpsimp;
      clarsimp simp: tcb_sched_dequeue_def valid_release_q_except_set_def valid_release_q_2_def)

lemma set_thread_state_sched_act_not_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and K (\<not>  runnable ts)
     and st_tcb_at (\<lambda>st. \<not> runnable st) thread\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: valid_sched_def |
      clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE |
      wp set_thread_state_not_runnable_valid_ready_qs
         set_thread_state_not_runnable_valid_blocked
         set_thread_state_not_runnable_valid_release_q
         set_thread_state_act_not_valid_sched_action)+

lemma set_thread_state_not_queued_valid_sched:
  "\<lbrace>valid_sched and (*simple_sched_action and*) not_in_release_q thread and
scheduler_act_not thread and not_queued thread and K (\<not>runnable ts)\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def |
      clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE |
      wp set_thread_state_not_queued_valid_ready_qs
         set_thread_state_not_runnable_valid_blocked
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
  by (wpsimp wp: set_thread_state_runnable_valid_ready_qs set_thread_state_runnable_valid_blocked
                    set_thread_state_runnable_valid_sched_action
                    set_thread_state_runnable_valid_release_q simp: valid_sched_def)

lemma set_thread_state_break_valid_sched:  (* ref is previously blocked *)
  "\<lbrace>valid_sched and K (runnable ts)\<rbrace>
      set_thread_state ref ts\<lbrace>\<lambda>_. valid_sched_except_blocked and valid_blocked_except ref::det_state \<Rightarrow> bool\<rbrace>"
  apply (wpsimp wp: set_thread_state_runnable_valid_sched_except_blocked
                    set_thread_state_valid_blocked_except)
  apply (simp add: valid_sched_def)
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

lemma set_thread_state_ct_valid_ep_q_inv:
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
  apply (clarsimp simp: valid_release_q_def st_tcb_at_kh_if_split)
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                      etcb_defs refill_prop_defs
               dest!: get_tcb_SomeD split: option.splits)

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
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_release_q_def st_tcb_at_kh_if_split)
  by (fastforce simp: valid_ready_qs_def st_tcb_at_kh_if_split not_in_release_q_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma set_tcb_sched_context_valid_ready_qs_Some: (* when ref is in ready_queeus *)
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>d p. ref \<in> set (ready_queues s d p) \<longrightarrow>
              test_sc_refill_max sp s \<and> is_refill_sufficient sp 0 s \<and>  is_refill_ready sp s)\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some sp) \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp dest!: get_tcb_SomeD split: option.splits
            simp: valid_ready_qs_def etcb_defs refill_prop_defs
                  st_tcb_at_kh_if_split active_sc_tcb_at_defs)
  by (intro impI conjI; fastforce dest!: get_tcb_SomeD simp: get_tcb_rev)+

lemma set_tcb_yield_to_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref ntfn \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
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
    (\<lambda>s. ref \<in> set (release_queue s) \<longrightarrow> test_sc_refill_max sp s)\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some sp) \<lbrace>\<lambda>_. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp dest!: get_tcb_SomeD split: option.splits
            simp: valid_release_q_def etcb_defs refill_prop_defs
                  st_tcb_at_kh_if_split active_sc_tcb_at_defs)
  by (intro impI conjI; fastforce dest!: get_tcb_SomeD simp: get_tcb_rev)+

lemma set_tcb_yield_to_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref ntfn \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_release_q_def st_tcb_at_kh_if_split)
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma set_bound_notification_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  done

lemma set_tcb_obj_ref_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> set_tcb_obj_ref f ref ntfn \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def)

lemma set_tcb_obj_ref_not_in_release_q[wp]:
  "\<lbrace>\<lambda>s. not_in_release_q t s\<rbrace> set_tcb_obj_ref f ref ntfn \<lbrace>\<lambda>_ s. not_in_release_q t s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def not_in_release_q_def)


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
  apply (clarsimp simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
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
  apply (clarsimp simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

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
                                    \<and> sc_refill_max sc > 0) scptr)\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some scptr)
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs  bound_sc_tcb_at_kh_if_split get_tcb_rev)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

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
                        scheduler_act_not_def dest!: get_tcb_SomeD)
   apply (rule_tac x= scp in exI, clarsimp)
  done

lemma set_tcb_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action
    and (\<lambda>s. scheduler_action s = switch_thread ref
             \<longrightarrow> (\<exists>scp. scp_opt = Some scp \<and> test_sc_refill_max scp s))\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref scp_opt
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  by (fastforce simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs get_tcb_rev
                        scheduler_act_not_def dest!: get_tcb_SomeD split: option.splits)

lemma set_tcb_sched_context_valid_sched_action_Some:
  "\<lbrace>valid_sched_action and (\<lambda>s. scheduler_action s = switch_thread ref \<longrightarrow>
          test_sc_refill_max scp s)\<rbrace>
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
 in_cur_domain_def active_sc_tcb_at_defs scheduler_act_not_def is_activatable_2_def
 etcb_defs switch_in_cur_domain_def dest!: get_tcb_SomeD split: option.splits)
  by (intro conjI impI; fastforce dest!: get_tcb_SomeD simp: get_tcb_rev)

lemma set_bound_notification_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.split)

lemma set_tcb_sched_context_valid_blocked_None:
  "\<lbrace>valid_blocked\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_sched_context_valid_blocked_Some:
  "\<lbrace>valid_blocked and
    (\<lambda>s. not_queued t s \<and> not_in_release_q t s \<longrightarrow> st_tcb_at (\<lambda>ts. \<not>runnable ts) t s \<or> \<not> test_sc_refill_max sp s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t (Some sp) \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  apply (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)
  by (case_tac "tcb_state y"; clarsimp)

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

lemma set_tcb_sched_context_valid_blocked_except_None:
  "\<lbrace>valid_blocked_except t\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
  apply (drule_tac x=ta in spec, clarsimp)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_tcb_yield_to_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)

lemma set_bound_notification_valid_ntfn_q:
  "\<lbrace>valid_ntfn_q\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_ntfn_q::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  apply (clarsimp simp: valid_ntfn_q_def
                 split: option.splits dest!: get_tcb_SomeD)
  by (rename_tac ko; case_tac ko;
      fastforce simp: active_sc_tcb_at_defs refill_prop_defs split: option.splits)

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

lemma set_sc_inv_test_sc_refill_max:
  "\<forall>sc. (sc_refill_max ((f (\<lambda>_. tptr)) sc) > 0) \<longleftrightarrow> (sc_refill_max sc > 0) \<Longrightarrow>
       \<lbrace>\<lambda>s. P (test_sc_refill_max scp s)\<rbrace>
     set_sc_obj_ref f ref tptr \<lbrace>\<lambda>_ s. P (test_sc_refill_max scp s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: test_sc_refill_max_def obj_at_def)

lemma set_sc_tcb_inv_test_sc_refill_max[wp]:
  "(*\<forall>sc. (sc_refill_max ((f (\<lambda>_. tptr)) sc) > 0) \<longleftrightarrow> (sc_refill_max sc > 0) \<Longrightarrow>*)
       \<lbrace>\<lambda>s. P (test_sc_refill_max scp s)\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_ s. P (test_sc_refill_max scp s)\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp set_sc_inv_test_sc_refill_max)

(* we don't need this
lemma set_sc_tcb_test_sc_refill_max[wp]:
  "\<lbrace>test_sc_refill_max scp\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. test_sc_refill_max scp\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: test_sc_refill_max_def obj_at_def)
*)

lemma set_sc_refills_inv_is_refill_sufficient:
  "\<forall>sc. sc_refills ((f (\<lambda>_. tptr)) sc) = sc_refills sc \<Longrightarrow>
       \<lbrace>is_refill_sufficient scp u\<rbrace>
     set_sc_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_sufficient scp u\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: is_refill_sufficient_def obj_at_def)

lemma set_sc_refills_inv_is_refill_ready:
  "\<forall>sc. sc_refills ((f (\<lambda>_. tptr)) sc) = sc_refills sc \<Longrightarrow>
       \<lbrace>is_refill_ready scp\<rbrace>
     set_sc_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_ready scp\<rbrace>"
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
  "\<lbrace>is_refill_ready scp\<rbrace>
     set_tcb_obj_ref f ref tptr \<lbrace>\<lambda>_. is_refill_ready scp\<rbrace>"
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

lemma set_tcb_sched_context_valid_sched_Some: (* what are the possible scenarios? *)
  "\<lbrace>valid_sched and tcb_at ref
    and (\<lambda>s. scheduler_action s = switch_thread ref
             \<longrightarrow> test_sc_refill_max scp s)
and (\<lambda>s. \<forall>d p. ref \<in> set (ready_queues s d p) \<longrightarrow>
              test_sc_refill_max scp s \<and> is_refill_sufficient scp 0 s \<and>  is_refill_ready scp s)
and (\<lambda>s. ref \<in> set (release_queue s) \<longrightarrow> test_sc_refill_max scp s)
and (\<lambda>s. not_queued ref s \<and> not_in_release_q ref s \<longrightarrow> st_tcb_at (\<lambda>ts. \<not>runnable ts) ref s \<or> \<not> test_sc_refill_max scp s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update ref (Some scp)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: set_tcb_sched_context_valid_ready_qs_Some
                 set_tcb_sched_context_valid_blocked_Some
                 set_tcb_sched_context_valid_release_q_Some
                 set_tcb_sched_context_valid_sched_action_Some
               simp : valid_sched_def)

(*
lemma set_tcb_sched_context_valid_sched:
  "\<lbrace>valid_sched and (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0) scptr)
     and is_refill_ready scptr and is_refill_sufficient scptr 0\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update ref (Some scptr) \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (si mp add: valid_sched_def test_sc_refill_max_def obj_at_def split: option.splits
                | wp set_tcb_sched_context_valid_ready_qs_Some set_tcb_sched_context_valid_release_q_Some
                     set_tcb_sched_context_valid_sched_action_Some)+ fastforce
*)
lemma set_tcb_yield_to_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_tcb_obj_ref tcb_yield_to_update ref scptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def
       | wp set_tcb_yield_to_valid_ready_qs
            set_tcb_yield_to_valid_sched_action)+
  done

crunch simple[wp]: set_sc_obj_ref,tcb_sched_action,update_sched_context,
set_tcb_obj_ref,tcb_release_remove,sched_context_donate simple_sched_action

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

lemma as_user_valid_release_q[wp]: "\<lbrace>valid_release_q\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_ready_qs_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split not_queued_def active_sc_tcb_at_defs
                etcb_defs refill_prop_defs dest!: get_tcb_SomeD split: option.splits)

lemma as_user_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

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
  apply (clarsimp simp: active_sc_tcb_at_defs  bound_sc_tcb_at_kh_if_split get_tcb_rev)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

lemma as_user_etcbs[wp]: "as_user ptr s \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: etcbs_of_update_unrelated)
  done

lemma as_user_ct_in_cur_domain[wp]: "\<lbrace>ct_in_cur_domain\<rbrace> as_user ptr s \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: etcbs_of_update_unrelated)
  done

lemma as_user_valid_blocked[wp]: "\<lbrace>valid_blocked\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
        split: option.splits dest!: get_tcb_SomeD)
  by (drule_tac x=t in spec, fastforce)

definition ct_in_q where
  "ct_in_q s \<equiv> st_tcb_at runnable (cur_thread s) s \<longrightarrow> (\<exists>d p. cur_thread s \<in> set (ready_queues s d p))"

locale DetSchedSchedule_AI =
  assumes arch_switch_to_idle_thread_valid_ready_qs'[wp]:
    "\<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  assumes arch_switch_to_thread_valid_ready_qs'[wp]:
    "\<And>t. \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_release_q'[wp]:
    "\<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  assumes arch_switch_to_thread_valid_release_q'[wp]:
    "\<And>t. \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
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
  assumes arch_switch_to_idle_thread_valid_idle[wp]:
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_idle::det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_ct_not_queued[wp]:
    "\<lbrace>valid_ready_qs and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  assumes make_arch_fault_msg_ct_not_queued[wp]:
    "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
      make_arch_fault_msg ft t
     \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  assumes make_arch_fault_msg_ct_not_in_release_q[wp]:
    "\<lbrace>\<lambda>s. not_in_release_q (cur_thread s) s\<rbrace>
      make_arch_fault_msg ft t
     \<lbrace>\<lambda>rv s::det_state. not_in_release_q (cur_thread s) s\<rbrace>"
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
  assumes arch_finalise_cap_ct_not_in_q'[wp]:
    "\<And>acap final. \<lbrace>ct_not_in_q\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_simple_sched_action'[wp]:
    "\<And>acap final. \<lbrace>simple_sched_action\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_valid_sched'[wp]:
    "\<And>acap final. \<lbrace>valid_sched\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_valid_sched'[wp]:
    "\<And>target ptr. \<lbrace>valid_sched\<rbrace> arch_tcb_set_ipc_buffer target ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_simple_sched_action'[wp]:
    "\<And>target ptr. \<lbrace>simple_sched_action\<rbrace> arch_tcb_set_ipc_buffer target ptr \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_valid_sched'[wp]:
    "\<And>f t x y. \<lbrace>valid_sched\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes activate_thread_valid_sched:
    "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_valid_sched[wp]:
    "\<And>i.
      \<lbrace>invs and valid_sched and ct_active and valid_arch_inv i\<rbrace>
        arch_perform_invocation i
      \<lbrace>\<lambda>_.valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_valid_sched'[wp]:
    "\<And>i. \<lbrace>valid_sched\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_valid_sched'[wp]:
    "\<And>t f. \<lbrace>valid_sched\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_not_queued'[wp]:
    "\<And>t' t f. \<lbrace>not_queued t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. not_queued t'::det_state \<Rightarrow> _\<rbrace>"
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
  assumes handle_arch_fault_reply_cur'[wp]:
    "\<And>f t x y. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. cur_tcb::det_state \<Rightarrow> _\<rbrace>"
  assumes hvmf_st_tcb_at[wp]:
    "\<And>P t' t w.
      \<lbrace>st_tcb_at P t' :: det_ext state \<Rightarrow> bool \<rbrace>
        handle_vm_fault t w
      \<lbrace>\<lambda>rv. st_tcb_at P t' \<rbrace>"
  assumes handle_vm_fault_st_tcb_cur_thread[wp]:
    "\<And>P t f.
      \<lbrace> \<lambda>s :: det_ext state. st_tcb_at P (cur_thread s) s \<rbrace>
        handle_vm_fault t f
      \<lbrace>\<lambda>_ s. st_tcb_at P (cur_thread s) s \<rbrace>"
  assumes arch_activate_idle_thread_valid_list'[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_list'[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_list'[wp]:
    "\<lbrace>valid_list\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_list::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_simple_sched_action'[wp]:
    "\<And>t. \<lbrace>simple_sched_action\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_not_cur_thread[wp] :
    "\<And>ft t t'. make_arch_fault_msg ft t \<lbrace>not_cur_thread t'::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_valid_sched[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_scheduler_action[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes make_fault_arch_msg_ready_queues[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes make_fault_arch_msg_release_queue[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (release_queue s)\<rbrace>"
  assumes make_fault_arch_msg_active_sc_tcb_at[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (active_sc_tcb_at t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_budget_ready[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (budget_ready t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_budget_sufficient[wp] :
    "\<And>P ft t t'. make_arch_fault_msg ft t' \<lbrace>(\<lambda>s. P (budget_sufficient t s))::det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_ct_active[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>ct_active::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_not_cur_thread[wp] :
    "\<And>ft t'. arch_get_sanitise_register_info ft \<lbrace>not_cur_thread t'::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_ct_not_queued[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>ct_not_queued::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_ct_not_in_release_q[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. not_in_release_q (cur_thread s) s\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_sched[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_sched::det_state \<Rightarrow> _\<rbrace>"
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
  assumes arch_post_cap_deletion_valid_ready_qs[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_release_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_ct_not_in_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>ct_not_in_q::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_simple_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>simple_sched_action::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_cur_thread[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_cur_thread t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_sched_act_not[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_queued[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_queued t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_in_release_q[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_weak_valid_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"


context DetSchedSchedule_AI begin

crunches switch_to_idle_thread, switch_to_thread
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action wp: hoare_drop_imp tcb_sched_action_dequeue_valid_ready_qs)

crunch weak_valid_sched_action[wp]:
  switch_to_idle_thread, switch_to_thread "weak_valid_sched_action::det_state \<Rightarrow> _"
  (simp: whenE_def wp: hoare_drop_imp)

end

lemma tcb_sched_action_dequeue_ct_not_in_q_2_ct_upd:
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

lemma tcb_sched_action_dequeue_valid_sched_action_2_ct_upd:
  "\<lbrace>valid_sched_action and
       (\<lambda>s. is_activatable_2 thread (scheduler_action s) (kheap s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. valid_sched_action_2 (scheduler_action s) (kheap s) thread (cur_domain s) (release_queue s)\<rbrace>"
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

lemma etcbs_of_arch_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_arch_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

context DetSchedSchedule_AI begin

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
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
      apply (clarsimp simp: valid_release_q_def active_sc_tcb_at_defs st_tcb_at_kh_if_split etcb_defs
                      split: option.splits dest!: get_tcb_SomeD)
      apply (drule_tac x=t in bspec; clarsimp dest!: get_tcb_SomeD)
      apply (intro conjI; clarsimp, rule_tac x=scp in exI, clarsimp)
     apply clarsimp
    apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split dest!: get_tcb_SomeD)
    apply (intro conjI impI allI; clarsimp simp: active_sc_tcb_at_defs split: option.splits)
     apply (rule_tac x=scp in exI, clarsimp)
    apply (rule_tac x=scp in exI, clarsimp)
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

end

lemma ct_not_in_q_def2:
  "ct_not_in_q_2 queues sa ct = (sa = resume_cur_thread \<longrightarrow> (\<forall>d p. ct \<notin> set (queues d p)))"
  by (fastforce simp add: ct_not_in_q_def not_queued_def)

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
  by (wpsimp wp: tcb_sched_action_dequeue_valid_sched_action_2_ct_upd hoare_drop_imp
          simp: switch_to_thread_def)

end

lemma tcb_sched_action_dequeue_ct_in_cur_domain':
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
  apply (wpsimp wp: tcb_sched_action_dequeue_ct_in_cur_domain' hoare_drop_imp)
  done

end

lemma ct_in_q_valid_blocked_ct_upd:
  "\<lbrakk>ct_in_q s; valid_blocked s\<rbrakk> \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  apply (clarsimp simp: valid_blocked_def ct_in_q_def)
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply (case_tac "t=cur_thread s")
   apply (simp add: not_queued_def)
   apply (case_tac st, (force simp: st_tcb_at_def obj_at_def)+)
   done

lemma tcb_sched_action_dequeue_valid_blocked':
  "\<lbrace>valid_blocked and ct_in_q\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_ s. valid_blocked (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  apply (simp add: tcb_sched_action_def, wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_blocked_def
                 dest!: ko_at_etcbD get_tcb_SomeD split: option.splits)
  apply (case_tac "t = cur_thread s")
   apply (simp add: ct_in_q_def)
   apply clarsimp
   apply (rule ccontr)
   apply clarsimp
   apply (erule impE)
    apply (case_tac st, (force simp: st_tcb_at_def obj_at_def)+)[1]
   apply force
  apply (erule_tac x=t in allE)
  apply force
  done

lemma ct_in_q_arch_state_upd[simp]:
  "ct_in_q (s\<lparr>arch_state := f\<rparr>) = ct_in_q s"
  by (simp add: ct_in_q_def)

lemma ct_in_q_machine_state_upd[simp]:
  "ct_in_q (s\<lparr>machine_state := f\<rparr>) = ct_in_q s"
  by (simp add: ct_in_q_def)

context DetSchedSchedule_AI begin
lemma as_user_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> as_user tp S \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
      dest!: get_tcb_SomeD split: option.splits)
  apply (rule conjI, fastforce)
  apply (case_tac "tp = cur_thread s"; clarsimp simp: ct_in_q_def obj_at_def pred_tcb_at_def)
  done
end

crunch ct_in_q[wp]: do_machine_op ct_in_q

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
  by (wpsimp wp: tcb_sched_action_dequeue_ct_in_cur_domain'
      tcb_sched_action_dequeue_valid_blocked' hoare_drop_imp)+

crunch etcb_at[wp]: switch_to_thread "etcb_at P t::det_state \<Rightarrow> _"
  (wp: hoare_drop_imp)

lemma switch_to_thread_valid_sched:
  "\<lbrace>is_activatable t and in_cur_domain t and valid_sched_action and valid_ready_qs and valid_release_q and
    valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def | wp | simp add: ct_in_cur_domain_2_def)+
  done

crunch valid_idle[wp]: switch_to_idle_thread "valid_idle :: det_ext state \<Rightarrow> bool"

crunch scheduler_action[wp]: switch_to_thread "\<lambda>s. P (scheduler_action (s :: det_ext state))"
  (wp: hoare_drop_imp)

end

crunches update_cdt_list
for valid_ready_qs[wp]: "valid_ready_qs"
and valid_release_q[wp]: "valid_release_q"
and ct_not_in_q[wp]: "ct_not_in_q"
and weak_valid_sched_action[wp]: "weak_valid_sched_action"
and valid_sched_action[wp]: "valid_sched_action"
and valid_blocked[wp]: valid_blocked
and valid_sched[wp]: "valid_sched"

crunches set_cdt, set_cap
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
and valid_release_q[wp]: "valid_release_q::det_state \<Rightarrow> _"
and ct_not_in_q[wp]: "ct_not_in_q::det_state \<Rightarrow> _"
and weak_valid_sched_action[wp]: "weak_valid_sched_action::det_state \<Rightarrow> _"
and valid_sched_action[wp]: "valid_sched_action::det_state \<Rightarrow> _"
and valid_blocked[wp]: "valid_blocked::det_state \<Rightarrow> _"
and valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
  (wp: valid_ready_qs_lift valid_release_q_lift ct_not_in_q_lift weak_valid_sched_action_lift
 valid_sched_action_lift valid_blocked_lift valid_sched_lift set_cap_typ_at)

crunch ct_not_in_q[wp]: cap_insert "ct_not_in_q :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps)

crunch weak_valid_sched_action[wp]: cap_insert "weak_valid_sched_action :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps)

lemma valid_ready_qs_trivial[simp]: "valid_ready_qs_2 (\<lambda>_ _. []) ctime kh"
  by (simp add: valid_ready_qs_def)

lemma valid_release_trivial[simp]: "valid_release_q_2 [] kh"
  by (simp add: valid_release_q_def)

lemma ct_not_in_q_trivial[simp]: "ct_not_in_q_2 (\<lambda>_ _. []) sa ct"
  by (simp add: ct_not_in_q_def not_queued_def)

lemma st_tcb_at_get_lift:
  "get_tcb thread s = Some y \<Longrightarrow> test (tcb_state y) \<Longrightarrow> st_tcb_at test thread s"
  by (simp add: ct_in_state_def st_tcb_def2)

lemmas det_ext_simps[simp] = select_switch_det_ext_ext_def unwrap_ext_det_ext_ext_def


lemma guarded_switch_to_lift:
  "\<lbrace>P\<rbrace> switch_to_thread thread \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> guarded_switch_to thread \<lbrace>Q\<rbrace>"
  by (wpsimp wp: get_sched_context_wp
           simp: guarded_switch_to_def is_schedulable_def get_thread_state_def thread_get_def)

lemma tcb_sched_action_lift:
  "(\<And>f s. P s \<Longrightarrow> P (ready_queues_update f s))
  \<Longrightarrow> \<lbrace>P\<rbrace> tcb_sched_action a b \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def etcb_at_def thread_get_def)

lemma next_domain_valid_idle[wp]:
  "\<lbrace> valid_idle \<rbrace> next_domain \<lbrace> \<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: next_domain_def wp: dxo_wp_weak)
  by (clarsimp simp: valid_idle_def Let_def)

definition next_thread where
  "next_thread queues \<equiv> (hd (max_non_empty_queue queues))"

lemma next_thread_update:
  assumes a: "P(next_thread queues)"
  assumes b: "P t"
  shows
    "P(next_thread (queues((p :: word8) := t # (queues prio))))"
proof -
  have imp_comp[simp]: "\<And>P Q. {x. P x \<longrightarrow> Q x} = {x. \<not> P x} \<union> {x. Q x}" by blast
  { assume c: "{prio. queues prio \<noteq> []} = {}"
    from a b c have ?thesis
      by (simp add: next_thread_def max_non_empty_queue_def)
  }
  moreover
  { assume d: "{prio. queues prio \<noteq> []} \<noteq> {}"
    from a b have ?thesis
      apply (clarsimp simp: next_thread_def
                            max_non_empty_queue_def
                            Max_insert[OF finite_word d])
      apply (clarsimp simp add: max_def)
      done
  }
  ultimately show ?thesis by blast
qed

lemma enqueue_thread_queued:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp s \<and> is_refill_sufficient scp 0 s)) thread s\<rbrace>
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
               \<and> (is_refill_ready scp s \<and> is_refill_sufficient scp 0 s)) thread s\<rbrace>
   tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. ready_queues s d prio \<noteq> [])\<rbrace>"
  by (rule hoare_post_imp[OF _ enqueue_thread_queued], metis empty_iff empty_set)

lemma next_thread_queued: "queues p \<noteq> [] \<Longrightarrow> \<exists>p. next_thread queues \<in> set (queues p)"
  apply (clarsimp simp: next_thread_def max_non_empty_queue_def)
  apply (rule_tac x="Max {prio. queues prio \<noteq> []}" in exI)
  apply (rule Max_prop)
   apply simp
  apply blast
  done

context DetSchedSchedule_AI begin

crunch etcb_at[wp]: switch_to_idle_thread "etcb_at P t :: det_state \<Rightarrow> _"

lemma switch_to_idle_thread_valid_sched:
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q
    and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp)+

crunch etcb_at[wp]: choose_thread "etcb_at P t :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma choose_thread_valid_sched[wp]:
  "\<lbrace>valid_sched_action and valid_idle and valid_ready_qs and valid_release_q
     and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
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
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def etcb_at_def)
  done

crunch ct_not_in_q: next_domain "ct_not_in_q" (simp: Let_def wp: dxo_wp_weak)

lemma next_domain_valid_sched_action:
  "\<lbrace>\<lambda>s. scheduler_action s = choose_new_thread\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: next_domain_def thread_set_domain_def)
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: Let_def valid_sched_action_def weak_valid_sched_action_def etcb_at_def)
  done

lemma tcb_sched_action_dequeue_in_cur_domain:
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
  apply (simp add: switch_to_thread_def | wp hoare_drop_imp tcb_sched_action_dequeue_in_cur_domain)+
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
crunch scheduler_action[wp]: switch_to_idle_thread, next_domain "\<lambda>s::det_state. P (scheduler_action s)"
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
  "\<lbrace>ct_not_in_q\<rbrace> reply_remove r \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)
  done

lemma etcbs_of'_non_tcb_update:
  "\<lbrakk> kh ref = Some obj'; a_type obj = a_type obj'; a_type obj \<noteq> ATCB \<rbrakk> \<Longrightarrow>
  etcbs_of' (\<lambda>a. if a = ref then Some obj else kh a) = etcbs_of' kh"
  by (rule ext) (auto simp: etcbs_of'_def split: kernel_object.splits)

lemma update_sched_context_valid_ready_qs:
  "\<lbrace>valid_ready_qs
     and (\<lambda>s. \<forall>t d p tcb. t \<in> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> sufficient_refills 0 (sc_refills (f sc))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs
                      active_sc_tcb_at_defs st_tcb_at_kh_if_split
               split: option.splits)

lemma update_sched_context_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs
     and (\<lambda>s. \<forall>t d p tcb. t \<notin> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref)\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: update_sched_context_def sc_tcb_sc_at_def obj_at_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ready_qs_def etcb_defs
                 split: option.splits)
  done

lemma update_sched_context_valid_ready_qs_not_bound:
  "\<lbrace>valid_ready_qs and
    (\<lambda>s. \<forall>t tcb. ko_at (TCB tcb) t s \<longrightarrow> tcb_sched_context tcb \<noteq> Some ref)\<rbrace>
       update_sched_context ref f \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  apply (simp add: update_sched_context_def sc_tcb_sc_at_def obj_at_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ready_qs_def etcb_defs
              split: option.splits)
  apply (drule_tac x=d and y=p in spec2, clarsimp)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  apply (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs
      active_sc_tcb_at_defs st_tcb_at_kh_if_split split: option.splits)
  done

lemma update_sched_context_valid_release_q:
  "\<lbrace>valid_release_q
     and (\<lambda>s. \<forall>t tcb. t \<in> set (release_queue s) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref
        \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow> 0 < sc_refill_max (f sc)))\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (fastforce simp: valid_release_q_def etcb_defs refill_prop_defs
    active_sc_tcb_at_defs st_tcb_at_kh_if_split split: option.splits)

lemma update_sched_context_valid_release_q_not_queued:
  "\<lbrace>valid_release_q
     and (\<lambda>s. \<forall>t tcb. t \<notin> set (release_queue s) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref)\<rbrace>
   update_sched_context ref f \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: update_sched_context_def sc_tcb_sc_at_def obj_at_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_release_q_def etcb_defs
                 split: option.splits)
  done

lemma update_sched_context_valid_release_q_not_bound:
  "\<lbrace>valid_release_q and
    (\<lambda>s. \<forall>t tcb. ko_at (TCB tcb) t s \<longrightarrow> tcb_sched_context tcb \<noteq> Some ref)\<rbrace>
       update_sched_context ref f \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  apply (simp add: update_sched_context_def sc_tcb_sc_at_def obj_at_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_release_q_def etcb_defs
              split: option.splits)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  apply (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs
      active_sc_tcb_at_defs st_tcb_at_kh_if_split split: option.splits)
  done

lemma update_sched_context_weak_valid_sched_action':
  "\<lbrace>weak_valid_sched_action and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
      update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  apply (rule conjI; clarsimp;
      rule_tac x=scp in exI, clarsimp)
  done

lemma update_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action
    and (\<lambda>s. \<forall>t tcb. scheduler_action s = switch_thread t \<and> ko_at (TCB tcb) t s
           \<and> tcb_sched_context tcb = Some ref
       \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow> 0 < sc_refill_max (f sc)))\<rbrace>
      update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: active_sc_tcb_at_defs bound_sc_tcb_at_kh_if_split get_tcb_rev)
  apply (rule conjI; clarsimp;
      rule_tac x=scp in exI, clarsimp)
  done

lemma update_sched_context_weak_valid_sched_action_act_not:
  "\<lbrace>weak_valid_sched_action and
    (\<lambda>s. \<forall>t tcb. scheduler_act_not t s \<and> ko_at (TCB tcb) t s \<and> tcb_sched_context tcb = Some ref)\<rbrace>
   update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  by (clarsimp simp: weak_valid_sched_action_def sc_tcb_sc_at_def obj_at_def scheduler_act_not_def
         dest!: get_tcb_SomeD)

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

lemma update_sched_context_valid_sched_action':
  "\<lbrace>valid_sched_action and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp update_sched_context_weak_valid_sched_action')+
  done

lemma update_sched_context_valid_sched_action:
  "\<lbrace>valid_sched_action
and (\<lambda>s. \<forall>t tcb. scheduler_action s = switch_thread t \<and> ko_at (TCB tcb) t s
           \<and> tcb_sched_context tcb = Some ref
     \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow> 0 < sc_refill_max (f sc)))\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp update_sched_context_weak_valid_sched_action)+
  done

lemma update_sched_context_valid_sched_action_act_not:
  "\<lbrace>valid_sched_action
and (\<lambda>s. \<forall>t tcb. scheduler_act_not t s \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref)
(* and (\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and> scheduler_act_not tp s) ref s)*)\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp update_sched_context_weak_valid_sched_action_act_not)+
  done

lemma update_sched_context_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     update_sched_context ptr f
   \<lbrace>\<lambda>_ . ct_in_cur_domain\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp set_scheduler_action_wp)
  apply (clarsimp simp: etcbs_of'_non_tcb_update a_type_def obj_at_def)
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

lemma update_sched_context_valid_blocked:
  "\<lbrace>valid_blocked and
   (\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow> (sc_refill_max sc > 0 \<longleftrightarrow> sc_refill_max (f sc) > 0))\<rbrace>
     update_sched_context ptr f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
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

lemma set_sc_ntfn_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_sc_obj_ref sc_ntfn_update p new \<lbrace>\<lambda>_. valid_ntfn_q\<rbrace>"
  unfolding set_sc_obj_ref_def update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: valid_ntfn_q_def obj_at_def split: option.splits)
  apply (rename_tac ko; case_tac ko; clarsimp)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs
               split: option.splits)

(*
lemma update_sched_context_valid_sched_not_queued_sched_act_not:
  "\<lbrace>valid_sched and K ((0 < sc_refill_max sc) = (0 < sc_refill_max (f sc)))
and (\<lambda>s. \<forall>t tcb. ko_at (TCB tcb) t s \<and> tcb_sched_context tcb = Some ref
  \<longrightarrow> scheduler_act_not t s \<and> (\<forall>d p. t \<notin> set (ready_queues s d p))
          \<and> t \<notin> set (release_queue s))
(*and (\<lambda>s. \<forall>t d p tcb. t \<notin> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
            \<and> t \<notin> set (release_queue s) \<and> tcb_sched_context tcb = Some ptr
            \<and> scheduler_act_not t s)*)
(*     and (\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp
                 \<and> not_queued tp s \<and> scheduler_act_not tp s) ptr s)*)\<rbrace>
    update_sched_context ptr f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_sched_def sc_tcb_sc_at_def obj_at_def
             wp: update_sched_context_valid_ready_qs_not_queued
                 update_sched_context_valid_release_q_not_queued
                 update_sched_context_valid_sched_action_act_not)
  apply (intro conjI allI; (drule_tac x=t in spec; fastforce)?)
*)
lemma update_sched_context_valid_sched:
  "\<lbrace>valid_sched and K (\<forall>sc. (0 < sc_refill_max sc) = (0 < sc_refill_max (f sc)))
    and (\<lambda>s. \<forall>t tcb. scheduler_action s = switch_thread t \<and> ko_at (TCB tcb) t s
                          \<and> tcb_sched_context tcb = Some ptr
       \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow> 0 < sc_refill_max (f sc)))
    and (\<lambda>s. \<forall>t d p tcb. t \<in> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
                           \<and> tcb_sched_context tcb = Some ptr
       \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow> 0 < sc_refill_max (f sc)
             \<and> sufficient_refills 0 (sc_refills (f sc))
             \<and> (r_time (refill_hd (f sc))) \<le> (cur_time s) + kernelWCET_ticks))
    and (\<lambda>s. \<forall>t tcb. t \<in> set (release_queue s) \<and> ko_at (TCB tcb) t s
                           \<and> tcb_sched_context tcb = Some ptr
       \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow> 0 < sc_refill_max (f sc)))
    and (\<lambda>s. \<forall>t tcb. ko_at (TCB tcb) t s \<and> tcb_sched_context tcb = Some ptr
       \<longrightarrow>  (\<forall>sc n. ko_at (SchedContext sc n) ptr s \<longrightarrow>
         ((0 < sc_refill_max sc) = (0 < sc_refill_max (f sc)))))\<rbrace>
    update_sched_context ptr f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def
             wp: update_sched_context_valid_ready_qs update_sched_context_valid_release_q
                 update_sched_context_valid_sched_action update_sched_context_valid_blocked)

lemma update_sched_context_valid_sched_not_queued:
  "\<lbrace>valid_sched and K (\<forall>sc. (0 < sc_refill_max sc) = (0 < sc_refill_max (f sc)))
 and (\<lambda>s. \<forall>t d p tcb. t \<notin> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
               \<and> scheduler_act_not t s \<and> tcb_sched_context tcb = Some ptr)
 and (\<lambda>s. \<forall>t tcb. t \<notin> set (release_queue s) \<and> ko_at (TCB tcb) t s
               \<and> scheduler_act_not t s \<and> tcb_sched_context tcb = Some ptr)
(* and (\<lambda>s. sc_tcb_sc_at (\<lambda>to. \<forall>tp. to = Some tp \<and>
                              not_queued tp s \<and> scheduler_act_not tp s) ptr s)*)\<rbrace>
    update_sched_context ptr f \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: valid_sched_def sc_tcb_sc_at_def obj_at_def
             wp: update_sched_context_valid_ready_qs_not_queued
                 update_sched_context_valid_release_q_not_queued
                 update_sched_context_valid_sched_action_act_not
                 update_sched_context_valid_blocked)

context DetSchedSchedule_AI begin

lemma choose_thread_ct_not_queued:
  "\<lbrace> valid_ready_qs and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

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
  by (simp add: ct_in_q_def)

lemma set_scheduler_action_cnt_simple[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. simple_sched_action \<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_obvious[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action a \<lbrace>\<lambda>_ s. scheduler_action s = a\<rbrace>"
  by (wpsimp wp: set_scheduler_action_wp)

lemma set_scheduler_action_cnt_valid_blocked':
  "\<lbrace>valid_blocked and (\<lambda>s. scheduler_action s = switch_thread t \<and>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread  \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply clarsimp
  apply (erule_tac x=ta in allE)
  apply (erule impCE)
   apply force
  apply (force simp: not_queued_def)
  done

lemma set_scheduler_action_cnt_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. scheduler_action s = switch_thread t \<and>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def wp: set_scheduler_action_cnt_valid_blocked'[where t=t])

lemma append_thread_queued:
  "\<lbrace>is_refill_sufficient thread 0\<rbrace>
     tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. thread \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: etcb_at_def tcb_sched_append_def obj_at_def is_refill_sufficient_def
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
                 wp: set_scheduler_action_rct_valid_sched choose_thread_ct_not_queued
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action next_domain_valid_release_q
                      next_domain_valid_ready_qs next_domain_valid_blocked next_domain_ct_in_q)+
  done


crunch valid_sched[wp]: cap_swap_for_delete, empty_slot "valid_sched :: det_state \<Rightarrow> _"
  (simp: unless_def wp: maybeM_inv ignore: set_object)

lemma update_sc_consumed_valid_sched:
  "\<lbrace>valid_sched\<rbrace> update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
      \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: get_object_wp simp: update_sched_context_def set_object_def)
  apply (clarsimp simp: valid_sched_def)
  apply (intro conjI)
      apply (fastforce simp: valid_ready_qs_def etcb_defs refill_prop_defs
       active_sc_tcb_at_defs st_tcb_at_kh_def  split: option.splits)
      apply (fastforce simp: valid_release_q_def etcb_defs refill_prop_defs
       active_sc_tcb_at_defs st_tcb_at_kh_def  split: option.splits)
     apply (clarsimp simp: valid_sched_action_def)
     apply (intro conjI)
       apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split obj_at_def pred_tcb_at_def)
      apply (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_if_split)
     apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs)
    apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_defs ct_in_cur_domain_def)
   apply (fastforce simp: valid_blocked_def st_tcb_at_kh_if_split active_sc_tcb_at_defs split: option.splits)
  apply (clarsimp simp: valid_idle_etcb_def etcb_defs)
  done

crunch valid_sched[wp]: commit_domain_time "valid_sched :: det_state \<Rightarrow> _"
  (ignore: update_sched_context simp: Let_def set_refills_def
    wp: update_sched_context_valid_ready_qs get_sched_context_wp hoare_drop_imp)

(* valid_sched for refill_split_check *)

lemma hd_last_length_2: "length ls = 2 \<Longrightarrow> [hd ls, last ls] = ls"
  apply (cases ls; clarsimp)
  by (case_tac list; clarsimp)

lemma refill_split_check_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> refill_split_check sc_ptr usage \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: refill_split_check_def)
  by (wpsimp wp: active_sc_tcb_at_update_sched_context_no_change
      simp: Let_def set_refills_def split_del: if_split)

lemma budget_sufficient_update_sched_context_no_budget_change:
  "\<lbrakk>\<And>x. sufficient_refills 0 (sc_refills (f x)) = sufficient_refills 0 (sc_refills x)\<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp:  update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: pred_tcb_at_def obj_at_def set_object_def wp: get_object_wp)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
  by (rule iffI conjI; fastforce simp: is_refill_sufficient_def obj_at_def split: if_split_asm)

lemma budget_ready_update_sched_context_no_time_change_gen:
  "\<lbrace>\<lambda>s. P (budget_ready t s)
    \<and> (\<forall>x.((r_time (hd (sc_refills (f x)))) \<le> (cur_time s) + kernelWCET_ticks) =
            ((r_time (hd (sc_refills x))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
     update_sched_context scp f \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp:  update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: pred_tcb_at_def obj_at_def set_object_def wp: get_object_wp)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
  apply (rule iffI conjI; auto simp: is_refill_ready_def obj_at_def split: if_split_asm)
  by (rule_tac x=scpa in exI; clarsimp)

lemma budget_ready_update_sched_context_no_time_change:
  "\<lbrace>\<lambda>s. P (budget_ready t s) \<and> (\<exists>sc n. ko_at (SchedContext sc n) scp s
    \<and> ((r_time (hd (sc_refills (f sc)))) \<le> (cur_time s) + kernelWCET_ticks) =
            ((r_time (hd (sc_refills sc))) \<le> (cur_time s) + kernelWCET_ticks))\<rbrace>
     update_sched_context scp f \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp:  update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: pred_tcb_at_def obj_at_def set_object_def wp: get_object_wp)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
  apply (rule iffI conjI; auto simp: is_refill_ready_def obj_at_def split: if_split_asm)
  by (rule_tac x=scpa in exI; clarsimp)+
(*
lemma valid_refills_sc_refill_max:
   "\<lbrakk>valid_refills scp budget s; ko_at (SchedContext sc n) scp s\<rbrakk>
     \<Longrightarrow> MIN_REFILLS \<le> sc_refill_max sc"
  by (fastforce simp: valid_refills_def obj_at_def)

lemma schedule_used_sufficient:
  "sufficient_refills 0 (refills @ [new]) \<Longrightarrow> sufficient_refills 0 (schedule_used refills new)"
  apply (induct refills arbitrary: new, simp)
  apply (clarsimp simp: sufficient_refills_def refills_capacity_def Let_def)
  done
*)
(*
lemma schedule_used_sufficient:
  "sufficient_refills 0 (refills @ [new]) \<Longrightarrow> sufficient_refills 0 (schedule_used refills new)"
  apply (induct refills arbitrary: new, simp)
  apply (clarsimp simp: sufficient_refills_def refills_capacity_def Let_def)
  oops

thm refill_split_check_def
thm refill_budget_check_def
lemma refill_split_check_budget_sufficient:
  notes schedule_used.simps[simp del]
  shows
  "\<lbrace>is_refill_sufficient sc_ptr 0 and valid_refills sc_ptr budget\<rbrace>
     refill_split_check sc_ptr usage \<lbrace>\<lambda>_ s. is_refill_sufficient sc_ptr 0 s\<rbrace>"
  apply (clarsimp simp: refill_split_check_def set_refills_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (case_tac "length (sc_refills sc) = sc_refill_max sc \<or> r_amount (refill_hd sc) - usage < MIN_BUDGET"; clarsimp split del: if_split)
   apply (case_tac "length (sc_refills sc) = Suc 0"; clarsimp)
 apply (wpsimp wp: hoare_vcg_if_lift2 set_object_wp get_object_wp
      simp: update_sched_context_def split_del: if_split)
apply (clarsimp simp: obj_at_def is_refill_sufficient_def sufficient_refills_def
 refills_capacity_def)
 apply (wpsimp wp: hoare_vcg_if_lift2 set_object_wp get_object_wp
      simp: update_sched_context_def Let_def split_del: if_split)
apply (clarsimp simp: obj_at_def is_refill_sufficient_def split del: if_split)
apply (rule schedule_used_sufficient)
apply (clarsimp simp: sufficient_refills_def refills_capacity_def)
defer
 apply (wpsimp wp: hoare_vcg_if_lift2 set_object_wp get_object_wp
      simp: update_sched_context_def Let_def split_del: if_split)
apply (clarsimp simp: obj_at_def is_refill_sufficient_def split del: if_split)
apply (rule schedule_used_sufficient)
apply (fastforce simp: sufficient_refills_def refills_capacity_def)
oops
*)


crunches refill_split_check
for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
and release_queue[wp]: "\<lambda>s. P (release_queue s)"
and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: crunch_wps)

lemma set_refills_valid_sched:
  "\<lbrace> valid_sched and test_sc_refill_max scp and K (sufficient_refills 0 refills)
     and (\<lambda>s. (r_time (hd refills)) \<le> (cur_time s) + kernelWCET_ticks)\<rbrace>
         set_refills scp refills \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_refills_def)
  apply (wpsimp wp: update_sched_context_valid_sched)
  by (fastforce simp: obj_at_def valid_sched_def test_sc_refill_max_def)

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

lemma switch_sched_context_valid_sched:
  "\<lbrace>valid_sched\<rbrace>
   switch_sched_context
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: switch_sched_context_def)
(*
  apply (wpsimp simp: refill_ready_def refill_sufficient_def
                  wp: hoare_drop_imps commit_time_valid_sched rollback_time_valid_sched
                      refill_unblock_check_valid_sched) *)
  sorry (* switch_sched_context_valid_sched *)

lemma set_next_timer_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_timer_interrupt thread_time \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_next_timer_interrupt_def)
  by wpsimp

lemma set_next_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_interrupt \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_next_interrupt_def)
  by (wpsimp wp: hoare_drop_imp)

lemma sc_and_timer_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sc_and_timer \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sc_and_timer_def)
  by (wpsimp simp: wp: switch_sched_context_valid_sched)

crunch ct_not_in_q[wp]: finalise_cap "ct_not_in_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp maybeM_inv
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

end

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and active_sc_tcb_at t and (\<lambda>s. t \<notin> set (release_queue s))
      and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  by (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_def
                   weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
       split: scheduler_action.splits) fastforce+

lemma possible_switch_to_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable target and active_sc_tcb_at target
    and not_cur_thread target
    and budget_ready target and budget_sufficient target (* really? *)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp simp: pred_tcb_at_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
  apply (wpsimp wp: reschedule_required_valid_blocked
                    set_scheduler_action_swt_weak_valid_sched
             split_del: if_split simp: not_in_release_q_def in_release_queue_def
         | strengthen valid_blocked_valid_blocked_except)+
  apply (clarsimp simp: pred_tcb_at_def etcb_at_def etcbs_of'_def in_cur_domain_def
               obj_at_def valid_sched_def valid_sched_action_def)
  done

lemma reschedule_required_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S\<rbrace> reschedule_required
   \<lbrace>\<lambda>rv. valid_blocked_except_set S :: det_state \<Rightarrow> bool\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
    apply ((wpsimp wp: set_scheduler_action_cnt_valid_blocked_except_set)+)[2]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac xa; clarsimp)
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except_set
                     tcb_sched_action_enqueue_valid_blocked_except_set_insert)
         apply (simp add: tcb_sched_action_def)
         apply (wpsimp simp: get_tcb_queue_def thread_get_def)+
   apply (clarsimp dest!: get_tcb_SomeD simp: get_tcb_rev)
    apply (clarsimp simp:  valid_blocked_except_def etcb_at_def split: option.splits)
   apply (clarsimp simp: obj_at_def)
   apply (rename_tac tcb scp sca na)
   apply (rule_tac x="tcb_domain tcb" in exI)
   apply (rule_tac x="tcb_priority tcb" in exI)
   apply (clarsimp simp: tcb_sched_enqueue_def)
  apply (wpsimp simp: set_scheduler_action_def)
  apply (clarsimp simp: is_schedulable_bool_def get_tcb_rev valid_blocked_except_set_def active_sc_tcb_at_def
      pred_tcb_at_def obj_at_def in_release_queue_def
      split: option.splits; drule_tac x=t in spec; clarsimp)
   apply (case_tac "x2=t"; clarsimp simp: get_tcb_rev)
  apply (case_tac "x2=t"; clarsimp simp: get_tcb_rev)
  apply (case_tac "tcb_state tcb"; clarsimp simp: not_in_release_q_def)
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
  "\<lbrace>valid_ready_qs (*and st_tcb_at runnable target and active_sc_tcb_at target
    and budget_ready target and budget_sufficient target*)
and (\<lambda>s. \<forall>tcb. ko_at (TCB tcb) target s \<and>
 tcb_domain tcb \<noteq> cur_domain s \<or> (tcb_domain tcb = cur_domain s \<and> scheduler_action s \<noteq> resume_cur_thread)
    \<longrightarrow> ( runnable (tcb_state tcb) \<and> active_sc_tcb_at target s \<and> budget_ready target s \<and> budget_sufficient target s))
\<rbrace>
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
  "\<lbrace>valid_ready_qs\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  by (wp hoare_drop_imps valid_ready_qs_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (wp hoare_drop_imps valid_release_q_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps switch_in_cur_domain_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps ct_in_cur_domain_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_lift | simp add: set_simple_ko_def)+

lemma possible_switch_to_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc; wpsimp)
  done

lemma possible_switch_to_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action and st_tcb_at runnable target and
    (bound_sc_tcb_at (\<lambda>sc. sc = None) target or active_sc_tcb_at target)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc)
     apply (wpsimp simp: set_scheduler_action_def | assumption)+
  by (clarsimp simp: weak_valid_sched_action_def pred_tcb_at_def obj_at_def not_in_release_q_def)

lemma possible_switch_to_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  unfolding possible_switch_to_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; case_tac inq; clarsimp simp: bind_assoc)
     by (wpsimp simp: set_scheduler_action_def|assumption)+

crunches possible_switch_to
for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

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
  "\<lbrace>valid_sched_action and st_tcb_at runnable target and active_sc_tcb_at target\<rbrace>
    possible_switch_to target \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
by (wpsimp simp: valid_sched_action_def)

crunches reply_unlink_sc,tcb_release_remove
  for etcb_at[wp]: "etcb_at P t"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches test_reschedule,tcb_release_remove
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches reply_unlink_tcb
  for etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

lemma valid_sched_scheduler_act_not:
  "valid_sched s \<Longrightarrow> st_tcb_at ((=) k) y s \<Longrightarrow> ~ runnable k \<Longrightarrow> scheduler_act_not y s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        scheduler_act_not_def st_tcb_at_def obj_at_def)

lemma reply_unlink_tcb_valid_sched:
  "\<lbrace>valid_sched \<rbrace>
   reply_unlink_tcb rptr
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched gts_wp get_simple_ko_wp)
  apply (intro conjI impI; clarsimp simp: reply_tcb_reply_at_def obj_at_def elim!: st_tcb_weakenE)
  apply (fastforce intro: valid_sched_scheduler_act_not)+
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

lemma refills_remove1_valid_sched[wp]:
  " \<lbrace>valid_sched\<rbrace>
    set_sc_obj_ref sc_replies_update scptr new
    \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_lift active_sc_tcb_at_update_sched_context_no_change
                budget_ready_update_sched_context_no_change budget_sufficient_update_sched_context_no_change
         simp: set_sc_obj_ref_def set_object_def)+

crunches update_sk_obj_ref,get_sk_obj_ref
  for valid_sched[wp]: "valid_sched:: det_state \<Rightarrow> _"

crunches get_sk_obj_ref
  for valid_ntfn_q[wp]: "valid_ntfn_q:: det_state \<Rightarrow> _"
  and valid_ep_q[wp]: "valid_ep_q:: det_state \<Rightarrow> _"

lemma reply_unlink_sc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_unlink_sc scptr rptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  apply (wpsimp wp: hoare_vcg_imp_lift get_simple_ko_wp)
  done

lemma reply_unlink_tcb_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace>
   reply_unlink_tcb rptr
   \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked gts_wp get_simple_ko_wp)

lemma reply_unlink_tcb_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
   reply_unlink_tcb rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: set_thread_state_not_runnable_valid_blocked gts_wp get_simple_ko_wp)

lemma set_scheduler_action_cnt_valid_blocked_except:
  "\<lbrace>\<lambda>s. valid_blocked_except target s
        \<and> (\<forall>t. scheduler_action s = switch_thread t \<longrightarrow> \<not> not_queued t s) \<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>rv. valid_blocked_except target::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  apply (fastforce simp: valid_blocked_except_def simple_sched_action_def
                   split: scheduler_action.splits)
  done

lemma tcb_sched_action_enqueue_valid_blocked_except_inv:
  "\<lbrace>valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread'
   \<lbrace>\<lambda>_. valid_blocked_except thread \<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "t=thread")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
   apply (case_tac "t=thread")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  done

lemma tcb_sched_action_enqueue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set (insert thread X)\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set X \<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def)
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "t\<in>X")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
   apply (case_tac "t\<in>X")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  done

lemma enqueue_thread_not_not_queued:
  "\<lbrace>\<lambda>s. t = thread \<and>
      bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
               \<and> (is_refill_ready scp s \<and> is_refill_sufficient scp 0 s)) thread s \<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. \<not> not_queued t s \<rbrace>"
  apply (simp add: tcb_sched_action_def not_queued_def)
  apply (wpsimp simp: thread_get_def)
  apply (fastforce simp: pred_tcb_at_def tcb_sched_enqueue_def
                        is_refill_ready_def obj_at_def is_refill_sufficient_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

crunch scheduler_action[wp]: tcb_sched_action "\<lambda>s. P (scheduler_action s)"

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
                           tcb_sched_action_enqueue_valid_blocked_except_inv
                           hoare_vcg_all_lift hoare_vcg_imp_lift enqueue_thread_not_not_queued)
         apply (wpsimp+)[4]
     apply (wpsimp simp: thread_get_def)
    apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def get_tcb_rev)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def is_refill_ready_def)
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except)
   apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def is_schedulable_opt_def
      active_sc_tcb_at_def pred_tcb_at_def obj_at_def in_release_queue_def get_tcb_rev)
  apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked_except)
  done

lemma set_scheduler_action_swt_weak_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
     and active_sc_tcb_at t and in_cur_domain t and simple_sched_action and (\<lambda>s. \<not> in_release_queue t s)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wpsimp
  by (force simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
     weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def not_in_release_q_def
     switch_in_cur_domain_def valid_blocked_def valid_blocked_except_def simple_sched_action_def
      split: scheduler_action.splits)

lemma set_scheduler_action_swt_weak_valid_sched_except_blocked:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except_set (insert t X) and st_tcb_at runnable t
     and active_sc_tcb_at t and in_cur_domain t and simple_sched_action and (\<lambda>s. \<not> in_release_queue t s)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_ s:: det_state. valid_sched_except_blocked s \<and> valid_blocked_except_set X s \<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wpsimp
  by (force simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
     weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def not_in_release_q_def
     switch_in_cur_domain_def valid_blocked_def valid_blocked_except_def simple_sched_action_def
      split: scheduler_action.splits)

definition has_budget where
  "has_budget t \<equiv> \<lambda>s. has_budget_kh t (cur_time s) (kheap s)"

lemma valid_nftn_qD1:
  "valid_ntfn_q s \<Longrightarrow>
   ko_at (Notification ntfn) ntfnptr s \<Longrightarrow>
   ntfn_obj ntfn = WaitingNtfn WNlist \<Longrightarrow>
   t \<in> set WNlist \<Longrightarrow>
   has_budget t s"
  apply (clarsimp simp: valid_ntfn_q_def obj_at_def has_budget_def)
  apply (drule_tac x = ntfnptr in spec)
  apply fastforce
  done

lemma valid_nftn_qD2:
  "valid_ntfn_q s \<Longrightarrow>
   ko_at (Notification ntfn) ntfnptr s \<Longrightarrow>
   ntfn_obj ntfn = WaitingNtfn WNlist \<Longrightarrow>
   t \<in> set WNlist \<Longrightarrow>
   not_cur_thread t s"
  apply (clarsimp simp: valid_ntfn_q_def obj_at_def has_budget_def not_cur_thread_def)
  apply (drule_tac x = ntfnptr in spec)
  apply fastforce
  done

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

lemma set_thread_state_has_budget[wp]:
  "\<lbrace>has_budget x\<rbrace>
   set_thread_state tcbptr ts
   \<lbrace>\<lambda>rv. has_budget x :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: has_budget_equiv2 wp: hoare_vcg_disj_lift)

lemma possible_switch_to_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)
    and (\<lambda>s. bound_sc_tcb_at bound target s
       \<longrightarrow> st_tcb_at runnable target s \<and> active_sc_tcb_at target s
           \<and> budget_ready target s \<and> budget_sufficient target s)\<rbrace>
     possible_switch_to target
    \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
   apply (clarsimp simp: valid_sched_def valid_blocked_def valid_blocked_except_def)
   apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
   apply (drule_tac x=t in spec, clarsimp)
   apply (case_tac "t=target"; clarsimp)
  apply (case_tac inq; clarsimp)
   apply wpsimp
   apply (fastforce simp: valid_sched_def valid_blocked_except_def not_in_release_q_def
                          in_release_queue_def valid_blocked_def)
  apply (wpsimp wp: set_scheduler_action_swt_weak_valid_sched'
                    reschedule_required_valid_blocked_except)
  by (fastforce simp: obj_at_def in_cur_domain_def etcb_defs pred_tcb_at_def)

lemma possible_switch_to_valid_sched3:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target
    and not_cur_thread target
    and st_tcb_at runnable target
    and has_budget target\<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def has_budget_equiv
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
   apply (clarsimp simp: valid_sched_def valid_blocked_def valid_blocked_except_def)
   apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
   apply (drule_tac x=t in spec, clarsimp)
   apply (case_tac "t=target"; clarsimp)
  apply (case_tac inq; clarsimp)
   apply wpsimp
   apply (fastforce simp: valid_sched_def valid_blocked_except_def not_in_release_q_def
                          in_release_queue_def valid_blocked_def)
  apply (wpsimp wp: set_scheduler_action_swt_weak_valid_sched'
                    reschedule_required_valid_blocked_except)
  by (fastforce simp: obj_at_def in_cur_domain_def etcb_defs pred_tcb_at_def)

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
      wp: set_scheduler_action_cnt_valid_blocked_except_set
      tcb_sched_action_enqueue_valid_blocked_except_set
      reschedule_required_valid_blocked_except_set
      set_scheduler_action_swt_weak_valid_sched_except_blocked[where X="S", simplified]
      wp_del: set_scheduler_action_valid_ready_qs
     | rule_tac Q="\<lambda>_. valid_sched_except_blocked and valid_blocked_except_set S"
          in hoare_strengthen_post)+
  by (fastforce simp: etcb_defs in_cur_domain_def obj_at_def pred_tcb_at_def split: option.splits)


crunches reply_unlink_tcb
for not_cur_thread[wp]: "not_cur_thread t"
and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
  (wp: crunch_wps)

definition schedulable_ep_thread_simple_2 where (* schedulable_ep_thread without thread_state condition *)
  "schedulable_ep_thread_simple_2 t ct it curtime kh =
       (t \<noteq> ct \<and> t \<noteq> it \<and>
         (bound_sc_tcb_at_kh ((=) None) t kh \<or>
        active_sc_tcb_at_kh t kh \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh))"

abbreviation schedulable_ep_thread_simple :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "schedulable_ep_thread_simple t s \<equiv>
     schedulable_ep_thread_simple_2 t (cur_thread s) (idle_thread s) (cur_time s) (kheap s)"

lemma set_simple_ko_schedulable_ep_thread_simple[wp]:
  "\<lbrace>\<lambda>s. schedulable_ep_thread_simple t s\<rbrace>
       set_simple_ko C ptr ep \<lbrace>\<lambda>rv s::det_state. schedulable_ep_thread_simple t s\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: partial_inv_def obj_at_def)
  apply (unfold schedulable_ep_thread_simple_2_def)
  apply (elim conjE disjE; simp)
   apply (intro impI conjI; rule disjI1,
      clarsimp simp: bound_sc_tcb_at_kh_if_split pred_tcb_at_def obj_at_def)
  by (intro impI conjI; rule disjI2,
      clarsimp simp: active_sc_tcb_at_kh_if_split active_sc_tcb_at_defs refill_prop_defs
               split: option.splits,
      intro conjI impI; fastforce?)

crunches possible_switch_to,set_thread_state_act
for schedulable_ep_thread_simple[wp]: "schedulable_ep_thread_simple t::det_state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

lemma set_thread_state_schedulable_ep_thread_simple[wp]:
  "\<lbrace>\<lambda>s. schedulable_ep_thread_simple t s\<rbrace>
       set_thread_state t' st \<lbrace>\<lambda>rv s::det_state. schedulable_ep_thread_simple t s\<rbrace>"
  apply (wpsimp simp: set_thread_state_def set_object_def wp: get_object_wp)
  apply (simp add: schedulable_ep_thread_simple_2_def)
  apply (elim conjE disjE)
   apply (clarsimp simp: active_sc_tcb_at_defs dest!: get_tcb_SomeD)
  apply (rule disjI2)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma reply_unlink_tcb_schedulable_ep_thread_simple[wp]:
  "\<lbrace>\<lambda>s. schedulable_ep_thread_simple t s\<rbrace>
       reply_unlink_tcb rp \<lbrace>\<lambda>rv s::det_state. schedulable_ep_thread_simple t s\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def  wp: gts_wp get_simple_ko_wp)

lemma valid_ep_q_imp_schedulable_ep_thread_simple:
  "\<lbrakk>t \<in> set queue; queue = ep_queue ep; ko_at (Endpoint ep) epptr s; valid_ep_q s\<rbrakk>
       \<Longrightarrow> schedulable_ep_thread_simple t s"
  apply (clarsimp simp: valid_ep_q_def)
  by (drule_tac x=epptr in spec, clarsimp simp: obj_at_def schedulable_ep_thread_simple_2_def)

lemma set_thread_state_bound_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t' s)\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv s. Q (bound_sc_tcb_at P t' s)\<rbrace>"
  apply (wpsimp simp: set_thread_state_def
                 wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)


lemma ball_mapM_x_scheme:  (* maybe move? is this generic enough? *)
  "\<And>Q P f xs.
   \<forall>t t'. \<lbrace> Q t' \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace> \<Longrightarrow>
      \<forall>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace> \<Longrightarrow>
            \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> mapM_x (\<lambda>t. f t) xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (rule_tac Q="\<lambda>_. (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P" in hoare_strengthen_post)
   apply (wp_once mapM_x_wp')
   apply (rule_tac Q="\<lambda>s. (Q x s \<and> (Q x s \<and> P s)) \<and> (\<lambda>s. \<forall>t\<in>set xs. Q t s) s" in hoare_weaken_pre)
    apply (rule_tac Q="\<lambda>_ s. (Q x s \<and> P s) \<and> (\<lambda>s. \<forall>t\<in>set xs. Q t s) s" in hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_vcg_conj_lift)
       apply (wpsimp simp: pred_conj_def)+
     apply (rule hoare_vcg_ball_lift)
     apply wpsimp
    apply simp+
  done

lemma cancel_all_ipc_valid_sched_helper0:
  "\<lbrace>schedulable_ep_thread_simple t and valid_sched\<rbrace>
      ( do st <- get_thread_state t;
               reply_opt <-
               case st of BlockedOnReceive x xa \<Rightarrow> return xa | _ \<Rightarrow> return None;
               y <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb (the reply_opt));
               y <- set_thread_state t Restart;
               possible_switch_to t
         od)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac st; clarsimp)
         defer 4
         apply ((wpsimp simp: has_budget_equiv2
                          wp: set_thread_state_runnable_valid_sched
                              set_thread_state_runnable_valid_ready_qs hoare_vcg_disj_lift
                              set_thread_state_runnable_valid_release_q
                              set_thread_state_runnable_valid_sched_action
                              set_thread_state_valid_blocked_except sts_st_tcb_at'
                              possible_switch_to_valid_sched3[simplified has_budget_equiv2]
                        cong: conj_cong,
                 clarsimp simp: valid_sched_def schedulable_ep_thread_simple_2_def
                                not_cur_thread_def)+)[7]
  by (wpsimp simp: has_budget_equiv2
               wp: set_thread_state_break_valid_sched
                   reply_unlink_tcb_valid_sched hoare_vcg_disj_lift
                   possible_switch_to_valid_sched3 sts_st_tcb_at' cong: conj_cong,
     clarsimp simp: valid_sched_def schedulable_ep_thread_simple_2_def not_cur_thread_def)

lemma cancel_all_ipc_valid_sched_helper1:
  "\<lbrace>schedulable_ep_thread_simple t'\<rbrace>
      ( do st <- get_thread_state t;
               reply_opt <-
               case st of BlockedOnReceive x xa \<Rightarrow> return xa | _ \<Rightarrow> return None;
               y <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb (the reply_opt));
               y <- set_thread_state t Restart;
               possible_switch_to t
         od)
  \<lbrace>\<lambda>_. schedulable_ep_thread_simple t'::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp)

lemma cancel_all_ipc_valid_sched_helper:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. schedulable_ep_thread_simple t s) and valid_sched\<rbrace>
       mapM_x (\<lambda>t. do st <- get_thread_state t;
                reply_opt <-
                case st of BlockedOnReceive x xa \<Rightarrow> return xa | _ \<Rightarrow> return None;
                y <- when (\<exists>y. reply_opt = Some y) (reply_unlink_tcb (the reply_opt));
                y <- set_thread_state t Restart;
                possible_switch_to t
             od) queue
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule ball_mapM_x_scheme)
  by (wpsimp wp: cancel_all_ipc_valid_sched_helper1 cancel_all_ipc_valid_sched_helper0)+

lemma cancel_all_ipc_valid_sched:
  "\<lbrace>valid_sched and valid_ep_q \<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp simp: get_ep_queue_def;
         (wpsimp wp: hoare_vcg_ball_lift | strengthen cancel_all_ipc_valid_sched_helper)+)
  by (auto simp: obj_at_def is_ep dest!: valid_ep_q_imp_schedulable_ep_thread_simple)

lemma cancel_all_signals_valid_sched_helper0:
  "\<lbrace>schedulable_ep_thread_simple t and valid_sched\<rbrace>
      ( do y <- set_thread_state t Restart;
           possible_switch_to t
        od)
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp simp: has_budget_equiv2
               wp: set_thread_state_break_valid_sched
                   possible_switch_to_valid_sched3 sts_st_tcb_at',
     clarsimp simp: valid_sched_def schedulable_ep_thread_simple_2_def not_cur_thread_def)

lemma cancel_all_signals_valid_sched_helper1:
  "\<lbrace>schedulable_ep_thread_simple t'\<rbrace>
      ( do y <- set_thread_state t Restart;
           possible_switch_to t
        od)
  \<lbrace>\<lambda>_. schedulable_ep_thread_simple t'::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: gts_wp)

lemma cancel_all_signals_valid_sched_helper:
  "\<lbrace>(\<lambda>s. \<forall>t\<in>set queue. schedulable_ep_thread_simple t s) and valid_sched\<rbrace>
       mapM_x (\<lambda>t.
             do y <- set_thread_state t Restart;
                possible_switch_to t
             od) queue
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule ball_mapM_x_scheme)
  by (wpsimp wp: cancel_all_signals_valid_sched_helper1 cancel_all_signals_valid_sched_helper0)+

lemma valid_ntfn_q_imp_schedulable_ep_thread_simple:
  "\<lbrakk>t \<in> set queue; ntfn_obj ntfn = WaitingNtfn queue; ko_at (Notification ntfn) ptr s; valid_ntfn_q s\<rbrakk>
       \<Longrightarrow> schedulable_ep_thread_simple t s"
  apply (clarsimp simp: valid_ntfn_q_def)
  by (drule_tac x=ptr in spec, clarsimp simp: obj_at_def schedulable_ep_thread_simple_2_def)

lemma cancel_all_signals_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_ntfn_q\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    defer 2
    apply (wpsimp+)[2]
  apply (rename_tac queue)
  apply (wpsimp wp: cancel_all_signals_valid_sched_helper hoare_vcg_ball_lift)
  by (rule valid_ntfn_q_imp_schedulable_ep_thread_simple)

crunches thread_set
for ready_queues[wp]:  "\<lambda>s. P (ready_queues s)"
and release_queue[wp]:  "\<lambda>s. P (release_queue s)"

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
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_priority (f x) = tcb_priority x;
    \<And>x. tcb_domain (f x) = tcb_domain x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
    \<lbrace>valid_release_q\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  by (rule valid_release_q_lift;
      wpsimp wp: thread_set_no_change_tcb_state thread_set_etcbs thread_set_active_sc_tcb_at)+

lemma thread_set_weak_valid_sched_action:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: weak_valid_sched_action_lift thread_set_no_change_tcb_state
                 active_sc_tcb_at_thread_set_no_change hoare_drop_imps
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

lemma set_sc_obj_ref_valid_ready_qs_not_queued:
  "\<lbrace>valid_ready_qs
and (\<lambda>s. \<forall>t d p tcb. t \<notin> set (ready_queues s d p) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref)\<rbrace>
        set_sc_obj_ref f ref new \<lbrace>\<lambda>_. valid_ready_qs\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def
         wp: update_sched_context_valid_ready_qs_not_queued)

lemma set_sc_obj_ref_valid_release_q_not_queued:
  "\<lbrace>valid_release_q
    and (\<lambda>s. \<forall>t tcb. t \<notin> set (release_queue s) \<and> ko_at (TCB tcb) t s
                                    \<and> tcb_sched_context tcb = Some ref)\<rbrace>
        set_sc_obj_ref f ref new \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def
         wp: update_sched_context_valid_release_q_not_queued)

lemma tcb_release_remove_not_in_release_q':
  "tcb_release_remove thread \<lbrace>not_in_release_q t \<rbrace>"
  by (wpsimp simp: tcb_release_remove_def not_in_release_q_def tcb_sched_dequeue_def)

crunches test_reschedule
for valid_ready_qs[wp]: "valid_ready_qs::det_state \<Rightarrow> _"
and not_in_release_q[wp]: "not_in_release_q t::det_state \<Rightarrow> _"
and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
and valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and test_sc_refill_max[wp]: "\<lambda>s. P (test_sc_refill_max p s)"
and is_refill_ready[wp]: "is_refill_ready p::det_state \<Rightarrow> _"
and is_refill_sufficient[wp]: "is_refill_sufficient p u::det_state \<Rightarrow> _"
and cur_time[wp]: "\<lambda>s. P (cur_time s)"
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

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
      tcb_sched_action_dequeue_valid_ready_qs tcb_dequeue_not_queued_gen
      simp: get_sc_obj_ref_def)

lemma sched_context_donate_valid_release_q_helper:
  "\<lbrace>valid_release_q and not_in_release_q tptr\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_release_q_not_queued)
   apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
      wp: get_object_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def valid_release_q_def etcb_defs not_in_release_q_def)
  apply (drule_tac x=t in bspec, simp)
  by (fastforce simp: valid_release_q_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
      refill_sufficient_kh_def refill_ready_kh_def
                is_refill_sufficient_def is_refill_ready_def
               dest!: get_tcb_SomeD split: option.splits)

lemma sched_context_donate_valid_release_q:
  "\<lbrace>valid_release_q and not_in_release_q tptr\<rbrace>
        sched_context_donate scptr tptr \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (case_tac from_opt; clarsimp)
   apply (wpsimp wp: sched_context_donate_valid_release_q_helper)
  apply (wpsimp wp: sched_context_donate_valid_release_q_helper
                    set_tcb_sched_context_valid_release_q_not_queued)
  by (wpsimp wp: tcb_release_remove_not_in_release_q')+

lemma set_tcb_sched_context_is_activatable[wp]:
  "\<lbrace>is_activatable t\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (wpsimp simp: is_activatable_def set_sc_obj_ref_def update_sched_context_def set_object_def
                wp: get_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

crunches set_sc_obj_ref
for valid_sched: "valid_sched::det_state \<Rightarrow> _"
and valid_ready_qs: "valid_ready_qs::det_state \<Rightarrow> _"
and valid_release_q: "valid_release_q::det_state \<Rightarrow> _"
and ct_in_cur_domain: "ct_in_cur_domain::det_state \<Rightarrow> _"
and valid_sched_action: "valid_sched_action::det_state \<Rightarrow> _"
and weak_valid_sched_action: "weak_valid_sched_action::det_state \<Rightarrow> _"
and switch_in_cur_domain[wp]: "switch_in_cur_domain::det_state \<Rightarrow> _"
and cur_activatable[wp]: "\<lambda>s::det_state. is_activatable (cur_thread s) s"

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

lemma set_sc_tcb_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_def)

lemma set_sc_ntfn_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def wp: get_object_wp)
  by (fastforce simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_def)

lemma set_sc_tcb_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by(wpsimp simp: valid_sched_action_def)

lemma set_sc_ntfn_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  by(wpsimp simp: valid_sched_action_def)

lemma set_sc_tcb_sched_context_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     set_sc_obj_ref sc_tcb_update ref tptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_sched_def
                  wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q
                     set_sc_obj_ref_ct_in_cur_domain)
  apply (rule conjI)
   apply (clarsimp simp: valid_ready_qs_def etcb_defs)
   apply (drule_tac x=d and y=p in spec2, clarsimp)
   apply (drule_tac x=t in bspec, simp, clarsimp)
   apply (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs refill_prop_defs
      dest!: get_tcb_SomeD split: option.splits)
  apply (clarsimp simp: valid_release_q_def etcb_defs)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  by (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma set_sc_ntfn_sched_context_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
     set_sc_obj_ref sc_ntfn_update ref tptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: valid_sched_def
                  wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q
                      set_sc_obj_ref_ct_in_cur_domain)
  apply (rule conjI)
   apply (clarsimp simp: valid_ready_qs_def etcb_defs)
   apply (drule_tac x=d and y=p in spec2, clarsimp)
   apply (drule_tac x=t in bspec, simp, clarsimp)
   apply (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs refill_prop_defs
      dest!: get_tcb_SomeD split: option.splits)
  apply (clarsimp simp: valid_release_q_def etcb_defs)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  by (fastforce simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs
               dest!: get_tcb_SomeD split: option.splits)

lemma tcb_release_remove_valid_sched_not_runnable:
  "\<lbrace>valid_sched and (\<lambda>s. \<not> (st_tcb_at active thread s \<and> active_sc_tcb_at thread s))\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_release_remove_valid_blocked)+

lemma tcb_release_remove_valid_sched_except_blocked:
  "\<lbrace>valid_sched\<rbrace>
     tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked::det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_release_remove_valid_blocked_except)+

lemma reply_unlink_tcb_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> reply_unlink_tcb param_a \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  by (wpsimp wp: gts_wp get_simple_ko_wp)

crunches set_mrs,set_message_info,set_consumed,reply_unlink_sc
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

lemma set_mrs_etcbs[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_mrs_def store_word_offs_def
  supply if_split [split del]
  by (wpsimp simp: zipWithM_x_mapM wp: mapM_wp' set_object_wp)

lemma set_sched_context_etcbs[wp]:
  "set_sched_context p sc \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  by (auto simp: obj_at_def etcbs_of'_def elim!: rsubst[where P=P])

lemma update_sched_context_etcbs[wp]:
  "update_sched_context p f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding update_sched_context_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  by (auto simp: obj_at_def etcbs_of'_def elim!: rsubst[where P=P])

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

lemma set_message_info_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def split_def set_object_def)

lemma set_message_info_budget_ready[wp]:
  "\<lbrace>(\<lambda>s. P (budget_ready t s))\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_ s. P (budget_ready t s)\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def split_def set_object_def)

lemma set_message_info_budget_sufficient[wp]:
  "\<lbrace>(\<lambda>s. P (budget_sufficient t s))\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_ s. P (budget_sufficient t s)\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def split_def set_object_def)

lemma set_mrs_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: wp: valid_sched_lift)

lemma set_message_info_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_message_info thread info \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp:  wp: valid_sched_lift)

crunches store_word_offs
  for active_sc_tcb_at[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
  (simp: zipWithM_x_mapM wp: dmo_active_sc_tcb_at mapM_wp' active_sc_tcb_at_set_object_no_change_sc ignore: set_sched_context)

lemma sched_context_donate_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (wpsimp simp: wp: get_sched_context_wp tcb_dequeue_not_queued_gen)
  done

lemma reply_remove_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and valid_objs\<rbrace>
     reply_remove rptr
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
for ct_in_cur_domain[wp]: ct_in_cur_domain
and valid_blocked[wp]: "valid_blocked :: det_state \<Rightarrow> _"
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

crunches thread_set, test_reschedule
for sched_act_not[wp]: "scheduler_act_not t"
  (wp: crunch_wps simp: crunch_simps)

declare test_reschedule_sched_act_not [wp del]

lemma sched_context_donate_valid_sched_action_NEW:
  "\<lbrace>valid_sched_action and scheduler_act_not tcb_ptr
    and (\<lambda>s. \<forall>sc n y. ko_at (SchedContext sc n) sc_ptr s \<longrightarrow> sc_tcb sc = Some y \<longrightarrow> scheduler_act_not y s)\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (wpsimp wp: hoare_vcg_if_lift2 set_tcb_sched_context_valid_sched_action_act_not
       get_sched_context_wp set_sc_tcb_valid_sched_action test_reschedule_sched_act_not)
  by (fastforce)

lemma sched_context_donate_simple_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  by (wpsimp wp: hoare_vcg_if_lift2 set_tcb_sched_context_valid_sched_action_act_not
       get_sched_context_wp set_sc_tcb_valid_sched_action test_reschedule_sched_act_not)

crunches sched_context_donate
for ct_in_cur_domain[wp]: "ct_in_cur_domain :: det_state \<Rightarrow> _"
  (wp: maybeM_wp hoare_drop_imp maybeM_wp hoare_vcg_if_lift2 ignore: sched_context_donate)

crunches test_reschedule,tcb_release_remove
for active_sc_tcb_at[wp]: "active_sc_tcb_at t"
and obj_at[wp]: "obj_at P p"
  (wp: crunch_wps ignore: set_object )

lemma set_tcb_queue_get_tcb[wp]:
 "\<lbrace>\<lambda>s. get_tcb t s = x\<rbrace> set_tcb_queue param_a param_b param_c \<lbrace>\<lambda>_ s. get_tcb t s = x\<rbrace> "
  by (wpsimp simp: set_tcb_queue_def get_tcb_def)

lemma get_tcb_release_queue_update[simp]: "get_tcb t (release_queue_update f s) = get_tcb t s"
  by (clarsimp simp: get_tcb_def)

lemma get_tcb_scheduler_action_update[simp]: "get_tcb t (scheduler_action_update f s) = get_tcb t s"
  by (clarsimp simp: get_tcb_def)

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

(* FIXME: Move *)
lemma set_object_obj:
  "\<lbrace>obj_at P ptr and K (x \<noteq> ptr)\<rbrace> set_object x ko \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  by (clarsimp simp add: valid_def set_object_def in_monad obj_at_def)

(* probably we don't need these:
lemma helper: "\<lbrace>\<lambda>s. (
                obj_at
                 (\<lambda>ko. \<exists>sc. (\<exists>n. ko = SchedContext sc n) \<and>
                             0 < sc_refill_max sc \<and> sc_tcb sc \<noteq> Some tcb_ptr)
                 sc_ptr)
                s \<and>
               (\<exists>n. ko_at (SchedContext sc n) sc_ptr s)\<rbrace>
          when (\<exists>y. sc_tcb sc = Some y)
           (do from_tptr <- assert_opt (sc_tcb sc);
               y <- tcb_sched_action tcb_sched_dequeue from_tptr;
               y <- tcb_release_remove from_tptr;
               y <- set_tcb_obj_ref tcb_sched_context_update from_tptr None;
               test_reschedule from_tptr
            od) \<lbrace>\<lambda>_ s. obj_at
                 (\<lambda>ko. \<exists>sc. (\<exists>n. ko = SchedContext sc n) \<and>
                             0 < sc_refill_max sc \<and> sc_tcb sc \<noteq> Some tcb_ptr)
                 sc_ptr
                s\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def tcb_sched_action_def
                wp: set_object_obj hoare_vcg_imp_lift)
  by (clarsimp simp: etcb_at_def pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD split: option.split)
(*  apply (wpsimp simp: set_tcb_obj_ref_def tcb_sched_action_def thread_get_def wp: hoare_drop_imp set_object_obj)*)
(*  by (clarsimp simp: etcb_at_def pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD split: option.split)
*)  (* this is obviously true with valid_objs *)

*)


crunch cur_thread[wp]: sched_context_donate  "\<lambda>s::det_state. P (cur_thread s)"
  (wp: crunch_wps maybeM_inv dxo_wp_weak simp: unless_def crunch_simps
   ignore: tcb_sched_action)

lemma set_sc_tcb_st_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace> set_sc_obj_ref sc_tcb_update sc tcb \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_sc_obj_ref_def set_object_def)
  apply wp
  done

lemma set_tcb_sched_context_valid_blocked_Some':
  "\<lbrace>valid_blocked and
    (\<lambda>s. not_queued t s \<and> not_in_release_q t s
             \<longrightarrow> st_tcb_at (\<lambda>ts. \<not>active ts) t s \<or> \<not> test_sc_refill_max sp s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t (Some sp) \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  by (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs dest!: get_tcb_SomeD
             split: if_split_asm option.splits)


lemma sched_context_donate_valid_blocked_helper:
  "\<lbrace>valid_blocked and st_tcb_at (\<lambda>ts. \<not> active ts) tptr\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_blocked_Some' get_object_wp
 simp: set_sc_obj_ref_def update_sched_context_def set_object_def)
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=tptr in spec, clarsimp simp: active_sc_tcb_at_defs split: if_splits option.splits)
  done

crunches test_reschedule
for weak_valid_sched_action[wp]: weak_valid_sched_action
and st_tcb_at[wp]: "st_tcb_at P t"
  (wp: hoare_vcg_if_lift2)

lemma tcb_release_remove_valid_blocked_except2:
  "\<lbrace>valid_blocked_except thread\<rbrace> tcb_release_remove thread \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def valid_blocked_except_def valid_blocked_def
                      tcb_sched_dequeue_def not_in_release_q_def)

lemma tcb_release_remove_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and K(thread \<in> S)\<rbrace>
   tcb_release_remove thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_release_remove_def valid_blocked_except_def valid_blocked_def
                      tcb_sched_dequeue_def not_in_release_q_def)
  by fastforce

lemma tcb_sched_dequeue_valid_blocked_except_set3:
  "\<lbrace>valid_blocked_except_set S and K(thread \<in> S)\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def valid_blocked_except_def valid_blocked_def
                      tcb_sched_dequeue_def not_in_release_q_def)
  apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "not_queued t s", fastforce)
  apply (clarsimp simp: not_queued_2_def)
  apply (drule_tac x = d in spec)
  apply (drule_tac x = p in spec)
  apply (case_tac "d = tcb_domain tcb \<and> p = tcb_priority tcb";
         clarsimp simp: in_queue_2_def)
  done

lemma sched_context_donate_valid_blocked:
  "\<lbrace>valid_blocked and st_tcb_at (\<lambda>ts.\<not> active ts) tcb_ptr
    and not_queued tcb_ptr and not_in_release_q tcb_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_blocked ::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (wpsimp wp: sched_context_donate_valid_blocked_helper
                    set_tcb_sched_context_valid_blocked_except_None
                   set_tcb_sched_context_weak_valid_sched_action
                   tcb_release_remove_valid_blocked_except2)
     by (wpsimp simp: set_object_def update_sched_context_def
               wp: get_object_wp set_tcb_sc_update_active_sc_tcb_at_neq
                   set_tcb_sched_context_weak_valid_sched_action_act_not
                   tcb_sched_action_dequeue_valid_blocked_except
                   tcb_sched_action_dequeue_valid_blocked
                   hoare_vcg_if_lift2 hoare_drop_imp
               split_del: if_split)+

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
  "\<lbrace>valid_sched and bound_sc_tcb_at ((=) None) tptr
    and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not>runnable ts) tptr s)\<rbrace>
     do y <- set_sc_obj_ref sc_tcb_update scptr (Some tptr);
        set_tcb_obj_ref tcb_sched_context_update tptr (Some scptr)
     od \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_Some hoare_vcg_imp_lift hoare_vcg_disj_lift
                    set_sc_refills_inv_is_refill_sufficient set_sc_refills_inv_is_refill_ready)
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

lemma reschedule_simple:"\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (clarsimp simp: reschedule_required_def, wpsimp)

lemma reschedule_cnt:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_ s. scheduler_action s = choose_new_thread\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  by (wpsimp simp: set_scheduler_action_def wp: thread_get_wp is_schedulable_wp
      wp_del: valid_idle_etcb_lift)
     (clarsimp simp: obj_at_def is_schedulable_opt_def dest!: get_tcb_SomeD split: option.splits)

declare reschedule_required_scheduler_act_not[wp del]

lemma set_scheduler_action_cnt_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma reschedule_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  by (wpsimp simp: reschedule_required_def)

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

(* maybe move? *)
abbreviation valid_sched_action_except_wk_sched_action_2 where
  "valid_sched_action_except_wk_sched_action_2 sa kh ct cdom rq\<equiv>
     is_activatable_2 ct sa kh \<and> switch_in_cur_domain_2 sa (etcbs_of' kh) cdom"

abbreviation valid_sched_action_except_wk_sched_action :: "'z state \<Rightarrow> bool" where
  "valid_sched_action_except_wk_sched_action s \<equiv> valid_sched_action_except_wk_sched_action_2 (scheduler_action s) (kheap s) (cur_thread s) (cur_domain s) (release_queue s)"

abbreviation valid_sched_except_blocked_except_wk_sched_action_2 where
  "valid_sched_except_blocked_except_wk_sched_action_2 queues sa cdom ctime kh ct it rq \<equiv>
    valid_ready_qs_2 queues ctime kh \<and> valid_release_q_2 rq kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_except_wk_sched_action_2 sa kh ct cdom rq \<and>
    ct_in_cur_domain_2 ct it sa cdom (etcbs_of' kh) \<and> valid_idle_etcb_2 (etcbs_of' kh)"

abbreviation valid_sched_except_blocked_except_wk_sched_action :: "det_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked_except_wk_sched_action s \<equiv>
   valid_sched_except_blocked_except_wk_sched_action_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s)
                                (cur_thread s) (idle_thread s) (release_queue s)"

definition weak_valid_sched_action_except_2 where
  "weak_valid_sched_action_except_2 thread sa kh release_q\<equiv>
    \<forall>t. t \<noteq> thread \<longrightarrow> sa = switch_thread t \<longrightarrow>
    st_tcb_at_kh runnable t kh \<and> (*bound_sc_tcb_at_kh bound t kh*)
    active_sc_tcb_at_kh t kh \<and> \<not> t \<in> set release_q"

abbreviation weak_valid_sched_action_except :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
 "weak_valid_sched_action_except t s \<equiv> weak_valid_sched_action_except_2 t (scheduler_action s) (kheap s) (release_queue s)"
(* end maybe move? *)


lemma set_tcb_sched_context_wk_valid_sched_action_except_None:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_tcb_obj_ref tcb_sched_context_update t None
       \<lbrace>\<lambda>_. weak_valid_sched_action_except t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  by (fastforce simp: weak_valid_sched_action_def weak_valid_sched_action_except_2_def
                      active_sc_tcb_at_defs st_tcb_at_kh_if_split
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
    apply ((wpsimp simp: valid_sched_def valid_sched_action_def)+)[2]
  apply (case_tac "t=x2"; clarsimp)
   defer
   apply (wpsimp simp: weak_valid_sched_action_def weak_valid_sched_action_except_2_def valid_sched_def
      valid_sched_action_def)
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
     apply (wpsimp wp: set_tcb_obj_ref_scheduler_act_not)
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

declare ssc_st_tcb_at[wp del] tcb_sched_action_st_tcb_at[wp del]

lemma ssc_st_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace> set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=Q] dest!: get_tcb_SomeD)
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma sched_context_donate_valid_sched_send_signal_WaitingNtfn_helper:
  notes test_reschedule_valid_sched[wp del]
  shows
  "\<lbrace>valid_sched\<rbrace>
        (do y <- tcb_sched_action tcb_sched_dequeue from_tptr;
            y <- tcb_release_remove from_tptr;
            y <-
            set_tcb_obj_ref tcb_sched_context_update from_tptr None;
            test_reschedule from_tptr
         od)
     \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (rule_tac Q="\<lambda>s. (valid_sched and scheduler_act_not from_tptr) s \<or>
  ((valid_sched and (\<lambda>s. scheduler_action s = switch_thread from_tptr)) s)" in hoare_weaken_pre)
   apply (rule_tac Q="\<lambda>_ s. valid_sched s \<or> valid_sched s" in hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift)
     apply (wpsimp wp: test_reschedule_valid_sched)
        apply (rule_tac Q="valid_sched_except_blocked and valid_blocked_except from_tptr
          and not_queued from_tptr and not_in_release_q from_tptr and scheduler_act_not from_tptr"
      in hoare_weaken_pre)
         apply (wpsimp simp: valid_sched_def
      wp: set_tcb_sched_context_valid_ready_qs_not_queued
      set_tcb_sched_context_valid_release_q_not_queued
      set_tcb_sched_context_valid_sched_action_act_not
      set_tcb_sched_context_valid_blocked_except_None)
        apply simp
       apply (wpsimp wp: tcb_release_remove_valid_blocked_except2 tcb_release_remove_not_in_release_q)
      apply (wpsimp wp: tcb_sched_action_dequeue_valid_blocked_except tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_ready_qs)
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
      tcb_sched_action_dequeue_valid_blocked_except
      hoare_vcg_imp_lift tcb_sched_action_st_tcb_at tcb_sched_action_dequeue_valid_ready_qs)
    apply (clarsimp simp: not_in_release_q_def in_release_queue_def)
    apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def)
   apply (clarsimp simp: scheduler_act_not_def)+
  done

lemma sched_context_donate_valid_sched:
  "\<lbrace>valid_sched and bound_sc_tcb_at ((=) None) tcb_ptr and st_tcb_at (\<lambda>x. \<not> runnable x) tcb_ptr\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp simp: )
   apply (wpsimp wp: sched_context_donate_valid_sched_helper)
  apply (rule hoare_seq_ext)
   apply (wpsimp wp: sched_context_donate_valid_sched_helper)
  apply (clarsimp simp: pred_conj_def)
  apply (rule hoare_vcg_conj_lift)
   apply (wpsimp wp: sched_context_donate_valid_sched_send_signal_WaitingNtfn_helper)
  by (wpsimp wp: Arch.test_reschedule_bound_sc_tcb_at (* move! *)
                    Arch.tcb_release_remove_bound_sc_tcb_at (* move! *)
                    ssc_bound_tcb_at_cases hoare_drop_imp tcb_dequeue_not_queued_gen
                    tcb_release_remove_not_in_release_q')+


lemma sched_context_donate_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace>
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: test_reschedule_sched_act_not)

(*
lemma sched_context_donate_simple_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and test_sc_refill_max sc_ptr
and (\<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> (st_tcb_at inactive a s)) sc_ptr s)\<rbrace>
(* I don't think it is possible to remove the inactive precondition *)
      sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_Some
                    set_tcb_sched_context_weak_valid_sched_action_act_not
      simp: tcb_sched_action_def)
     apply (wpsimp wp: set_tcb_sched_context_valid_sched_neq_None
                       tcb_sched_action_dequeue_valid_sched_not_runnable tcb_dequeue_not_queued)+
  apply (clarsimp simp: etcb_at_def sc_tcb_sc_at_def obj_at_def valid_sched_def
                  split: option.splits cong: conj_cong)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done
*)

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

lemma reply_unlink_sc_tcb_tcb_inactive:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>
   reply_unlink_tcb rp
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (\<lambda>t. \<forall>a. t = Some a \<longrightarrow> st_tcb_at inactive a s) scp' s\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac state)
  apply (case_tac state; clarsimp simp: assert_def)
   apply (wpsimp simp: set_simple_ko_def set_object_def
      wp: sts_sc_tcb_sc_at_inactive get_object_wp)
   apply (clarsimp simp: partial_inv_def sc_tcb_sc_at_def obj_at_def)
   apply (case_tac "scp'\<noteq>rp"; clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (wpsimp simp: set_simple_ko_def set_object_def
      wp: sts_sc_tcb_sc_at_inactive get_object_wp)
  apply (clarsimp simp: partial_inv_def sc_tcb_sc_at_def obj_at_def)
  apply (case_tac "scp'\<noteq>rp"; clarsimp simp: pred_tcb_at_def obj_at_def)
  done

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

lemma reply_unlink_sc_test_sc_refill_max[wp]:
  "reply_unlink_sc sp rp \<lbrace>\<lambda>s::det_state. P (test_sc_refill_max t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_sc_def)

lemma reply_unlink_tcb_test_sc_refill_max[wp]:
  "reply_unlink_tcb rp \<lbrace>\<lambda>s::det_state. P (test_sc_refill_max t s)\<rbrace>"
  by (wpsimp wp: get_simple_ko_wp gts_wp simp: reply_unlink_tcb_def)

(* FIXME: Move *)
lemma st_tcb_reply_state_refs:
  "\<lbrakk>valid_objs s; sym_refs (state_refs_of s); st_tcb_at ((=) (BlockedOnReply (Some rp))) thread s\<rbrakk>
  \<Longrightarrow> \<exists>reply. (kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some thread)"
  apply (frule (1) st_tcb_at_valid_st2)
  apply (drule (1) sym_refs_st_tcb_atD[rotated])
  apply (clarsimp simp: get_refs_def2 obj_at_def valid_tcb_state_def is_reply
                  split: thread_state.splits if_splits)
  done

crunches update_sk_obj_ref,get_sk_obj_ref
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"

lemma reply_unlink_sc_active_sc_tcb_at[wp]:
 "\<lbrace>active_sc_tcb_at t\<rbrace>
     reply_unlink_sc scp rptr \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  by (wpsimp wp: hoare_vcg_imp_lift get_simple_ko_wp)

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

text {* The reply a TCB is waiting on *}
definition
  reply_blocked :: "thread_state \<Rightarrow> obj_ref option"
where
  "reply_blocked ts \<equiv> case ts of
     BlockedOnReceive ep (Some r) \<Rightarrow> Some r
   | BlockedOnReply (Some r) \<Rightarrow> Some r
   | _ \<Rightarrow> None"

(*
lemma reply_unlink_sc_no_tcb_update[wp]:
  "\<lbrace> ko_at (TCB v) t
    and K (reply_blocked (tcb_state v) \<noteq> Some rp )
(*and reply_tcb_reply_at (\<lambda>p. p \<noteq> Some t) rp*)
\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. ko_at (TCB v) t\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def assert_opt_def assert_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp simp: reply_blocked_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac ts)
  apply (case_tac ts; clarsimp simp: pred_tcb_at_def pred_conj_def obj_at_def)
  apply (wpsimp simp: set_object_def set_thread_state_def set_simple_ko_def
         wp: get_object_wp get_simple_ko_wp hoare_drop_imp)
  apply (case_tac "tcb_state v
  apply (clarsimp simp: a_type_def partial_inv_def obj_at_def reply_tcb_reply_at_def)
  apply (rule conjI; clarsimp)
  apply (drule_tac x=v' in spec)
  by (fastf orce simp: a_type_def partial_inv_def obj_at_def)
*)

lemma reply_remove_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t and valid_objs and (\<lambda>s. sym_refs (state_refs_of s))
    and (\<lambda>s. reply_sc_reply_at (\<lambda>p. \<forall>scp. p = Some scp
             \<longrightarrow> sc_tcb_sc_at (\<lambda>x. x \<noteq> Some t) scp s) rptr s) (* callee *)\<rbrace>
     reply_remove rptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp simp: assert_opt_def)
  apply (wpsimp wp: sched_context_donate_active_sc_tcb_at_neq gbn_wp
                    static_imp_wp hoare_vcg_if_lift2)
  apply (rename_tac sc_ptr sc n)
  apply (drule(1) valid_objs_ko_at)
  subgoal for _ _ _ sc_ptr sc
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
     reply_remove rp
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
     reply_remove_tcb tp
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: reply_remove_valid_sched reply_unlink_tcb_valid_sched)
  done

lemma set_ntfn_sc_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_ntfn_obj_ref ntfn_sc_update ptr ep \<lbrace>\<lambda>rv. valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
                  wp: get_object_wp get_simple_ko_wp)
  apply (case_tac ko; clarsimp simp: a_type_def partial_inv_def obj_at_def)
  apply (clarsimp simp: valid_ntfn_q_def split: option.splits)
  apply (intro conjI impI; clarsimp)
  apply (rename_tac ko; case_tac ko; clarsimp)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs
               split: option.splits)

lemma set_ntfn_bound_tcb_valid_ntfn_q[wp]:
  "\<lbrace>valid_ntfn_q\<rbrace> set_ntfn_obj_ref ntfn_bound_tcb_update ptr ep \<lbrace>\<lambda>rv. valid_ntfn_q:: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def
      wp: get_object_wp get_simple_ko_wp)
  apply (case_tac ko; clarsimp simp: a_type_def partial_inv_def obj_at_def)
  apply (clarsimp simp: valid_ntfn_q_def split: option.splits)
  apply (intro conjI impI; clarsimp)
  apply (rename_tac ko; case_tac ko; clarsimp)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs
               split: option.splits)

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
  apply (clarsimp simp: sched_context_update_consumed_def set_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def split: if_splits)
  apply (rule conjI; clarsimp)
  apply (rule_tac x=scpa in exI, clarsimp)+
  done

lemma sched_context_update_consumed_budget_sufficient[wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def set_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def split: if_splits)
  apply (rule conjI; clarsimp)
   apply (rule_tac x=scpa in exI, fastforce)+
  done

lemma sched_context_update_consumed_budget_ready[wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def set_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def split: if_splits)
  apply (rule conjI; clarsimp)
   apply (rule_tac x=scpa in exI, fastforce)+
  done

crunches set_consumed
for active_sc_tcb_at[wp]: "\<lambda>s. P (active_sc_tcb_at t (s::det_state))"
and budget_sufficient[wp]: "\<lambda>s::det_state. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s::det_state. P (budget_ready t s)"

lemma set_consumed_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_consumed scp buf \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: valid_sched_lift split_del: if_split)

lemma complete_yield_to_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> complete_yield_to tp \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def get_sk_obj_ref_def)
              apply (wpsimp simp: set_tcb_obj_ref_def wp: hoare_drop_imp)+
  by (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def set_tcb_obj_ref_def)+

(*
crunch valid_sched[wp]: sched_context_unbind_all_tcbs,sched_context_clear_replies,suspend valid_sched
  (wp: valid_sched_lift ignore: tcb_release_remove set_tcb_queue)
*)

lemma thread_set_fault_simple_sched_action[wp]:
  "\<lbrace> simple_sched_action \<rbrace> thread_set (tcb_fault_update u) t \<lbrace>\<lambda>rv. simple_sched_action \<rbrace>"
  by (wpsimp wp: ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            simp: thread_set_def)

lemma reply_cancel_ipc_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
     reply_cancel_ipc tptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (wpsimp wp: thread_set_not_state_valid_sched reply_remove_tcb_valid_sched)
  done

lemma cancel_signal_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s) and simple_sched_action\<rbrace>
     cancel_signal tptr ntfnptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched hoare_drop_imps)
  done

crunch st_tcb_at_not_runnable[wp]: reply_cancel_ipc "st_tcb_at (\<lambda>st. \<not>runnable st) t::det_state \<Rightarrow> _"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps wp_del: reply_remove_st_tcb_at)

lemma blocked_cancel_ipc_valid_sched_Send:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s) and simple_sched_action\<rbrace>
     blocked_cancel_ipc (BlockedOnSend ep data) tptr None
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched simp: get_blocking_object_def)
  done

lemma blocked_cancel_ipc_valid_sched_Receive:
  "\<lbrace>valid_sched
    and simple_sched_action
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
      simp: set_simple_ko_def set_object_def)
   apply (clarsimp simp: simple_sched_action_def scheduler_act_not_def
      split: scheduler_action.split_asm elim!: st_tcb_weakenE)
  apply (wpsimp wp: set_thread_state_not_runnable_valid_sched get_simple_ko_wp
      reply_unlink_tcb_valid_sched get_object_wp
      simp: set_simple_ko_def set_object_def)
  apply (clarsimp cong: conj_cong simp: partial_inv_def)
  apply (rule conjI)
   defer
   apply (clarsimp simp: simple_sched_action_def scheduler_act_not_def
      reply_tcb_reply_at_def obj_at_def pred_tcb_at_def
      split: scheduler_action.split_asm)
    apply (case_tac "tcb_state tcb"; clarsimp)
   apply (case_tac "tcb_state tcb"; clarsimp)
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
    apply (clarsimp simp: valid_release_q_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
    apply (intro conjI impI, fastforce)
    apply (clarsimp simp: active_sc_tcb_at_defs)
    apply (drule_tac x=t in bspec, simp, clarsimp)
    apply (rename_tac scp)
    apply (rule_tac x=scp in exI, clarsimp)
   apply (clarsimp simp: valid_sched_action_def, rule conjI)
    apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
   apply (intro impI conjI; fastforce?)
   apply (clarsimp simp: active_sc_tcb_at_defs)
   apply (rule_tac x=scp in exI, fastforce)
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
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s)) and simple_sched_action and valid_sched\<rbrace>
      cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift reply_cancel_ipc_valid_sched
      blocked_cancel_ipc_valid_sched_Receive blocked_cancel_ipc_valid_sched_Send)
   by (fastforce elim!: st_tcb_weakenE)+

end

(* valid_ready_qs with thread not runnable *)
lemma tcb_sched_action_dequeue_strong_valid_sched:
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

lemma reschedule_required_valid_blocked_except_weak:
  "\<lbrace>valid_blocked\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_blocked_except t::det_state \<Rightarrow> bool\<rbrace>"
  by (rule hoare_strengthen_post, rule reschedule_required_valid_blocked) simp

lemma reschedule_required_valid_blocked_except_set_weak:
  "\<lbrace>valid_blocked\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_blocked_except_set S::det_state \<Rightarrow> bool\<rbrace>"
  by (rule hoare_strengthen_post, rule reschedule_required_valid_blocked) simp

lemma possible_switch_to_valid_blocked: (* check preconditions *)
  "\<lbrace>valid_blocked\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: tcb_sched_action_enqueue_valid_blocked reschedule_required_valid_blocked thread_get_wp
      simp: set_scheduler_action_def get_tcb_obj_ref_def)
  apply (clarsimp simp: obj_at_def valid_blocked_def pred_tcb_at_def)
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
  by (clarsimp simp: obj_at_def)

crunches set_scheduler_action,possible_switch_to
for budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
and not_in_release_q[wp]: "not_in_release_q t"
  (wp: crunch_wps)

crunch simple[wp]: update_sk_obj_ref,reply_unlink_sc,reply_unlink_tcb,reply_remove simple_sched_action
  (simp: a_type_def wp: hoare_drop_imps)

lemma sched_context_unbind_tcb_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp reschedule_simple)

lemma set_thread_state_in_cur_domain[wp]:
  "set_thread_state p st \<lbrace>in_cur_domain t\<rbrace>"
  by (rule hoare_lift_Pf[where f=etcbs_of], rule hoare_lift_Pf[where f=cur_domain]; wp)

crunch simple[wp]: unbind_from_sc,sched_context_unbind_all_tcbs simple_sched_action
  (wp: maybeM_wp crunch_wps hoare_vcg_all_lift)

crunches cancel_ipc
for simple_sched_action[wp]: simple_sched_action
and scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: maybeM_wp hoare_drop_imps)

crunches unbind_maybe_notification, unbind_notification,
         sched_context_maybe_unbind_ntfn, reply_unlink_sc,
         sched_context_unbind_ntfn
for  not_queued[wp]: "not_queued t"
and not_in_release_q'[wp]: "\<lambda>s:: det_state. P (not_in_release_q t s)"
and  scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: crunch_wps maybeM_inv simp: get_sc_obj_ref_def)

crunches blocked_cancel_ipc,cancel_signal
for not_queued[wp]: "not_queued t"
and not_in_release_q[wp]: "not_in_release_q t:: det_state \<Rightarrow> _"
  (wp: hoare_drop_imp simp: )

lemma reply_cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> reply_cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t:: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: reply_cancel_ipc_def)

lemma cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t:: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; wpsimp)
  done

context DetSchedSchedule_AI begin

crunch simple[wp]: suspend,sched_context_unbind_ntfn simple_sched_action
  (wp: maybeM_wp hoare_drop_imps)

(*
crunch simple_sched_action[wp]: cancel_all_ipc, finalise_cap simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl maybeM_wp set_thread_state_simple
   simp: unless_def if_fun_split)
*)

lemma in_set_tcb_sched_dequeue:
  "t \<in> set (tcb_sched_dequeue k (ready_queues s a b)) \<Longrightarrow>
   t \<in> set (ready_queues s a b) \<and> t \<noteq> k"
 by (auto simp: tcb_sched_dequeue_def)

(* FIXME: move *)
lemma the_get_tcb:
  "kheap s t = Some (TCB tcb) \<Longrightarrow> the (get_tcb t s) = tcb"
  by (clarsimp simp: get_tcb_def)

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
   apply (fastforce simp: obj_at_def is_tcb the_get_tcb dest!: get_tcb_SomeD)
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

lemma sc_yield_from_update_valid_sched_parts:
  "\<lbrace>valid_sched_action\<rbrace> set_sc_obj_ref sc_yield_from_update a b \<lbrace>\<lambda>rv s::det_state. valid_sched_action s\<rbrace>"
  "\<lbrace>valid_blocked\<rbrace> set_sc_obj_ref sc_yield_from_update a b \<lbrace>\<lambda>rv s::det_state. valid_blocked s\<rbrace>"
   apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_valid_sched_action')
  apply (wpsimp simp: set_sc_obj_ref_def wp: update_sched_context_valid_blocked')
  done

lemma tcb_yield_to_update_in_ready_q:
  "\<lbrace>in_ready_q t\<rbrace> set_tcb_obj_ref tcb_yield_to_update a b \<lbrace>\<lambda>rv s::det_state. in_ready_q t s\<rbrace>"
   apply (wpsimp simp: set_tcb_obj_ref_def wp: update_sched_context_valid_sched_action')
  done

crunch not_in_release_q[wp]: cancel_ipc "not_in_release_q t:: det_state \<Rightarrow> _"
  (simp: crunch_simps  wp: crunch_wps tcb_release_remove_not_in_release_q')

lemma tcb_sched_dequeue_not_active:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>\<lambda>s. (st_tcb_at active t s \<longrightarrow> \<not> active_sc_tcb_at t s)\<rbrace>"
  unfolding tcb_sched_action_def
  by wpsimp

lemma tcb_sched_dequeue_valid_release_q_except[wp]:
  "tcb_sched_action tcb_sched_dequeue t \<lbrace>valid_release_q_except t\<rbrace>"
  unfolding tcb_sched_action_def
  by wpsimp

lemma suspend_valid_sched:
  "\<lbrace>valid_objs and valid_sched and (\<lambda>s. sym_refs (state_refs_of s)) and simple_sched_action and tcb_at t\<rbrace>
      suspend t
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: suspend_def maybeM_def valid_sched_def)
  apply (wpsimp wp: tcb_release_remove_valid_blocked tcb_release_remove_valid_release_q_except)
  apply (wpsimp wp: tcb_sched_action_dequeue_valid_blocked tcb_sched_action_dequeue_valid_ready_qs'
                    tcb_sched_dequeue_not_active)
      apply (wpsimp wp: set_thread_state_inactive_valid_ready_queues_sp
                        set_thread_state_valid_release_q_except
                        set_thread_state_act_not_valid_sched_action
                        set_thread_state_not_runnable_valid_blocked set_thread_state_not_active_helper)
     apply (wpsimp)
      apply (wpsimp wp: set_tcb_yield_to_valid_sched_action set_tcb_yield_to_valid_ready_qs tcb_yield_to_update_in_ready_q)
     apply (wpsimp wp: set_sc_obj_ref_valid_ready_qs set_sc_obj_ref_valid_release_q set_sc_obj_ref_ct_in_cur_domain
                       sc_yield_from_update_valid_sched_parts)
    apply (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp)
   apply (rule hoare_strengthen_post[where Q="\<lambda>r. valid_sched and
              scheduler_act_not t and tcb_at t"])
    apply (wpsimp wp: cancel_ipc_valid_sched)
   apply (clarsimp simp: valid_sched_def obj_at_def is_tcb split: option.splits)
   apply (intro conjI)
    apply (intro impI allI)
    apply (clarsimp simp: valid_ready_qs_def dest:exE)
    apply (intro conjI;
           simp add: active_sc_tcb_at_def test_sc_refill_max_def is_refill_sufficient_def
                     is_refill_ready_def;
           fastforce simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: valid_release_q_def dest:exE)
   apply (simp add: active_sc_tcb_at_def test_sc_refill_max_def;
          fastforce simp: pred_tcb_at_def obj_at_def)
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
                    tcb_sched_action_dequeue_valid_ready_qs tcb_sched_action_dequeue_valid_blocked_except tcb_dequeue_not_queued
                    reschedule_required_valid_blocked reschedule_act_not)
  apply (clarsimp simp: valid_sched_def)
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

lemma fast_finalise_valid_sched:
  "\<lbrace>valid_sched and valid_objs and simple_sched_action and (\<lambda>s. sym_refs (state_refs_of s))
     and valid_ep_q and valid_ntfn_q\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  apply (cases cap;
      clarsimp;
      wpsimp wp: cancel_all_ipc_valid_sched cancel_ipc_valid_sched get_simple_ko_wp
                 reply_remove_valid_sched gts_wp)
  apply (frule(2) st_tcb_reply_state_refs; clarsimp simp: pred_tcb_at_eq_commute)
  apply (clarsimp simp: pred_tcb_at_def reply_tcb_reply_at_def obj_at_def)
  done

lemma cap_delete_one_valid_sched:
  "\<lbrace>valid_sched and valid_objs and simple_sched_action and (\<lambda>s. sym_refs (state_refs_of s))
    and valid_ep_q and valid_ntfn_q\<rbrace>
   cap_delete_one (a, b)
   \<lbrace>\<lambda>y. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: fast_finalise_valid_sched get_cap_wp)

lemma deleting_irq_handler_valid_sched:
  "\<lbrace>valid_sched and valid_objs and simple_sched_action and (\<lambda>s. sym_refs (state_refs_of s))
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
  "\<lbrace>valid_sched and simple_sched_action and invs and valid_cap cap
    and valid_ep_q and valid_ntfn_q\<rbrace>
   finalise_cap cap param_b
   \<lbrace>\<lambda>_. valid_sched:: det_state \<Rightarrow> _\<rbrace>"
  apply (case_tac cap; (solves \<open>wpsimp\<close>)?; simp)
       apply (wpsimp wp: cancel_all_ipc_valid_sched cancel_ipc_valid_sched get_simple_ko_wp)
      apply (wpsimp wp: cancel_ipc_valid_sched reply_remove_valid_sched gts_wp get_simple_ko_wp)
      apply (safe; clarsimp)
      apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_eq_commute)
      apply (subgoal_tac "\<exists>reply. (kheap s xb = Some (Reply reply) \<and> reply_tcb reply = Some x)")
       apply (clarsimp simp: runnable_def st_tcb_at_def obj_at_def)
      apply (rule_tac st_tcb_reply_state_refs[OF invs_valid_objs invs_sym_refs];
             clarsimp simp: pred_tcb_at_eq_commute)
     apply (intro conjI impI;  wpsimp)
    apply (intro conjI impI; wpsimp wp: suspend_valid_sched)
      apply (rule_tac Q="\<lambda>ya. valid_sched and invs and (\<lambda>s. simple_sched_action s \<and> tcb_at x7 s)"
                      in hoare_strengthen_post)
       apply (wpsimp wp: unbind_from_sc_valid_sched Arch.unbind_from_sc_invs Arch.unbind_from_sc_tcb_at)
      apply fastforce
     apply (wpsimp wp: unbind_notification_invs)
    apply (clarsimp simp: valid_cap_def)
  apply (intro conjI impI; wpsimp wp: deleting_irq_handler_valid_sched)
  apply fastforce
  done

end

crunch simple_sched_action[wp]: cap_swap_for_delete, cap_insert simple_sched_action

context DetSchedSchedule_AI begin

crunch simple_sched_action[wp]: empty_slot simple_sched_action

crunches unbind_maybe_notification, sched_context_maybe_unbind_ntfn,
  sched_context_unbind_yield_from, sched_context_unbind_reply
for simple_sched_action[wp]: simple_sched_action
  (wp: crunch_wps simp: crunch_simps)

crunches finalise_cap
for simple_sched_action: simple_sched_action
  (wp: crunch_wps reschedule_simple possible_switch_to_simple_sched_action)

(* This depends on finalise_cap_valid_sched and finalise_cap_simple_sched_action
   Check they are complete first *)
lemma rec_del_valid_sched'[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
    rec_del call
   \<lbrace>\<lambda>rv. valid_sched and simple_sched_action\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wpsimp wp: preemption_point_inv' finalise_cap_simple_sched_action)+
  sorry (* rec_del *)

lemma rec_del_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule rec_del_valid_sched')
  apply simp
  done


lemma rec_del_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wpsimp wp: rec_del_preservation preemption_point_inv' finalise_cap_simple_sched_action)

crunches cap_delete
for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and simple_sched_action[wp]: simple_sched_action

end

crunches tcb_sched_action
for ct_in_state[wp]: "ct_in_state P"
and not_pred_tcb[wp]: "\<lambda>s. \<not> pred_tcb_at proj P t s"

lemma ct_in_state_def2: "ct_in_state test s = st_tcb_at test (cur_thread s) s"
   by (simp add: ct_in_state_def)

crunches reorder_ntfn,reorder_ep
  for valid_sched[wp]:"valid_sched::det_state \<Rightarrow> _"
  and simple_sched_action[wp]: simple_sched_action
  (wp: mapM_wp' get_simple_ko_wp)

lemma thread_set_priority_neq_st_tcb_at[wp]:
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
  "\<lbrace>valid_release_q\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: valid_release_q_def etcb_defs active_sc_tcb_at_defs st_tcb_at_kh_def
               split: option.splits dest!: get_tcb_SomeD)

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
                 dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp)+
    apply force
   apply (rule_tac x=scp in exI, fastforce)
  apply (rule conjI; clarsimp)+
   apply (rule_tac x=scp in exI, fastforce)
  apply (rule_tac x=scp in exI, fastforce)
  done

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
  "thread_set_priority p t \<lbrace>valid_blocked_except t'\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: valid_blocked_except_def st_tcb_at_kh_def active_sc_tcb_at_defs
                   split: option.splits dest!:get_tcb_SomeD)

lemma thread_set_priority_valid_blocked[wp]:
  "thread_set_priority p t \<lbrace>valid_blocked\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: valid_blocked_def st_tcb_at_kh_def active_sc_tcb_at_defs
                   split: option.splits dest!:get_tcb_SomeD)

lemma thread_set_priority_weak_valid_sched_action[wp]:
  "thread_set_priority t p \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def active_sc_tcb_at_defs st_tcb_at_kh_def
                 dest!: get_tcb_SomeD)
  apply (rule conjI; clarsimp)+
   apply force
  apply (rule_tac x=scp in exI, fastforce)
  done

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
  "\<lbrace>valid_sched and not_queued t(* and not_in_release_q t*)\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_sched\<rbrace>"
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
lemma tcb_sched_action_dequeue_valid_sched_in_release_queue:
  "\<lbrace>valid_sched and in_release_queue thread and ready_or_released\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched::det_state\<Rightarrow>_\<rbrace>"
  apply (wpsimp wp: tcb_sched_action_dequeue_valid_sched_not_queued)
  by (simp add: ready_or_released_in_release_queue)

lemma set_priority_valid_sched[wp]:
  "\<lbrace>valid_sched and not_cur_thread tptr and budget_ready tptr
    and budget_sufficient tptr and ready_or_released\<rbrace>
   set_priority tptr prio
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_priority_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp simp: bind_assoc)
    (* schedulable *)
   apply (wpsimp wp: tcb_sched_action_dequeue_valid_sched_except_blocked
      tcb_dequeue_not_queued thread_set_priority_valid_ready_qs_not_q
      tcb_sched_action_dequeue_valid_blocked_except hoare_drop_imp
      tcb_sched_action_enqueue_valid_sched thread_set_priority_valid_release_q_not_q
      tcb_sched_action_dequeue_valid_ready_qs
      cong: conj_cong)
   apply (clarsimp simp: is_schedulable_bool_def valid_sched_def get_tcb_rev active_sc_tcb_at_def
      pred_tcb_at_def obj_at_def in_release_queue_def not_in_release_q_def
      split: option.splits)
    (* not schedulable *)
      (* in_release_queue *)
  apply (clarsimp simp: is_schedulable_bool_def)
  apply (case_tac in_release_q; clarsimp)
   apply (wpsimp wp: tcb_sched_action_dequeue_valid_sched_in_release_queue hoare_drop_imp
      tcb_dequeue_not_queued cong: conj_cong)
   apply (clarsimp simp: is_schedulable_bool_def pred_tcb_at_def obj_at_def get_tcb_rev valid_sched_def
      split: option.splits)
    (* not in_release_queue *)
  apply (wpsimp wp: hoare_drop_imp tcb_sched_action_dequeue_valid_sched_not_runnable tcb_dequeue_not_queued
      cong: conj_cong)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev active_sc_tcb_at_def valid_sched_def runnable_eq_active)
  done

lemma set_mcpriority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mcpriority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

crunch simple_sched_action[wp]: set_mcpriority,thread_set_priority simple_sched_action
  (wp: maybeM_inv)

lemma set_priority_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_priority param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: set_priority_def wp: maybeM_inv)

lemma set_tcb_sched_context_valid_sched_except_blocked_None:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and (\<lambda>s. t \<noteq> idle_thread s)
     and not_queued t and not_in_release_q t and simple_sched_action\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update t None \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_sched_def dest!: get_tcb_SomeD)
  apply (intro conjI)
       apply (clarsimp simp: valid_ready_qs_def etcb_defs not_queued_def
      active_sc_tcb_at_defs st_tcb_at_kh_if_split refill_prop_defs
      split: option.splits)
       apply (drule_tac x=d and y=p in spec2, clarsimp)
       apply (drule_tac x=ta in bspec, simp, fastforce)
      apply (clarsimp simp: valid_release_q_def etcb_defs not_in_release_q_def
      active_sc_tcb_at_defs st_tcb_at_kh_if_split
      split: option.splits)
      apply (drule_tac x=ta in bspec, simp, fastforce)
     apply (fastforce simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def get_tcb_rev
      simple_sched_action_def st_tcb_at_kh_if_split active_sc_tcb_at_defs
      etcb_defs switch_in_cur_domain_def
      split: option.splits)
    apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcb_defs get_tcb_rev)
   apply (clarsimp simp: valid_blocked_def valid_blocked_except_def st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
      split: option.splits if_splits)
   apply (drule_tac x=ta in spec)
   apply (clarsimp simp: st_tcb_at_kh_if_split active_sc_tcb_at_defs get_tcb_rev
      split: option.splits)
  apply (clarsimp simp: valid_idle_etcb_def etcb_defs get_tcb_rev split: option.splits)
  done

lemma sched_context_unbind_tcb_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action
   and (\<lambda>s. sc_tcb_sc_at (\<lambda>p. \<exists>tp. p = Some tp \<and> tp \<noteq> idle_thread s) sc_ptr s)\<rbrace>
      sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_tcb_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: set_tcb_sched_context_valid_sched_except_blocked_None
                   tcb_release_remove_valid_blocked_except2
                   tcb_sched_action_dequeue_valid_blocked_except tcb_dequeue_not_queued
                   reschedule_required_valid_blocked tcb_sched_action_dequeue_valid_ready_qs
                   tcb_release_remove_not_in_release_q)
  by (clarsimp simp: valid_sched_def sc_tcb_sc_at_def obj_at_def)
  (* need to introduce the notion of idle_sc? *)

lemma get_sc_time_sp:
  "\<lbrace>P\<rbrace> get_sc_time thread
        \<lbrace>\<lambda>rv. P and (\<lambda>s. bound_sc_tcb_at (\<lambda>p. \<exists>scp. p = Some scp
                          \<and> (\<exists>sc n. ko_at (SchedContext sc n) scp s
                                  \<and> r_time (refill_hd sc) = rv)) thread s)\<rbrace>"
  apply (clarsimp simp: get_sc_time_def get_tcb_sc_def assert_opt_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rename_tac tcb_sc)
  apply (case_tac tcb_sc; clarsimp)
  apply (rename_tac scp)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply wpsimp
  by (clarsimp simp: pred_tcb_at_def obj_at_def, rule_tac x=scp in exI, fastforce)

lemma release_queue_cong':
  "set queue = set (release_queue s) \<Longrightarrow> distinct queue \<Longrightarrow> distinct (release_queue s) \<Longrightarrow>
    valid_sched_2  (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s) (cur_thread s)
                  (idle_thread s) queue
      = valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s) (cur_thread s)
                  (idle_thread s) (release_queue s)"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

lemma release_queue_cong:
  "set queue = set queue' \<Longrightarrow> distinct queue \<Longrightarrow> distinct queue' \<Longrightarrow>
    valid_sched_2  (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s) (cur_thread s)
                  (idle_thread s) queue
      = valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s) (cur_thread s)
                  (idle_thread s) queue'"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

lemma release_queue_cong2:
  "set queue = set queue' \<Longrightarrow> distinct queue \<Longrightarrow> distinct queue' \<Longrightarrow>
    valid_release_q_2  queue (kheap s) = valid_release_q_2  queue' (kheap s)"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

lemma valid_sched_release_queue_update[simp]:
  "set queue = set (release_queue s) \<Longrightarrow> distinct queue \<Longrightarrow> distinct (release_queue s) \<Longrightarrow>
    valid_sched (s\<lparr>release_queue:=queue\<rparr>) = valid_sched s"
  by (clarsimp simp: valid_sched_def valid_release_q_def valid_sched_action_def
                     weak_valid_sched_action_def valid_blocked_def not_in_release_q_def)

(* FIXME move *)
lemma set_filter_all[simp]: "set (filter (\<lambda>x. P x) xs @ filter (\<lambda>x. \<not> P x) xs) = set xs" by auto

(* FIXME move *)
lemma set_shuffle_left: "set (ls @ t # ls') = set (t # ls @ ls')"
  by auto

(* FIXME move *)
lemma mapM_length_eq:
  "\<lbrace>\<top>\<rbrace> mapM f xs \<lbrace>\<lambda>rv. K (length xs = length rv)\<rbrace>"
  apply (induct xs, wpsimp simp: mapM_Nil)
  by (wpsimp simp: mapM_Cons mapM_def sequence_def|assumption)+

(* FIXME move *)
lemma mapM_wp_inv_length:
  "(\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv s. P s \<and> (length xs = length rv)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_vcg_conj_lift[OF _ mapM_length_eq[simplified]])
   apply (wpsimp wp: mapM_wp_inv, auto)
  done


(* FIXME move *)
lemma sorted_eq_original_as_set:
  "length qs = length ps \<Longrightarrow>
       set (map fst (filter (\<lambda>(p, t'). t' \<le> time) (zip qs ps)) @
                map fst (filter (\<lambda>(p, t'). \<not> t' \<le> time) (zip qs ps)))
       = set qs"
  apply (simp only: map_append[symmetric] set_map set_filter_all split_def)
  apply (simp only: set_map[symmetric] map_fst_zip)
  done

lemma distinct_zip_fun:
  "\<lbrakk>distinct xs; (a, b) \<in> set (zip xs ys); (a, b') \<in> set (zip xs ys)\<rbrakk>
     \<Longrightarrow> b = b'"
  apply (induct xs arbitrary: ys, simp)
  apply (clarsimp simp: zip_Cons1)
  apply (erule disjE, fastforce dest!: in_set_zipE)
  apply (erule disjE, fastforce dest!: in_set_zipE, clarsimp)
  done

lemma tcb_release_enqueue_valid_sched:
  "\<lbrace> not_queued thread and not_in_release_q thread
    and scheduler_act_not thread
    and valid_sched_except_blocked and valid_blocked_except thread
    and st_tcb_at runnable thread and active_sc_tcb_at thread\<rbrace>
      tcb_release_enqueue thread \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s)
            (cur_time s) (kheap s) (cur_thread s) (idle_thread s) (thread # qs)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: release_queue_cong')
   defer
   apply (clarsimp simp: valid_sched_def, intro conjI)
      apply (clarsimp simp: valid_release_q_def etcb_defs not_in_release_q_def
                       pred_tcb_at_def obj_at_def split: option.splits)
     apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def scheduler_act_not_def)
    apply (clarsimp simp: valid_blocked_def valid_blocked_except_set_def)
    apply (drule_tac x=t in spec, clarsimp simp: not_in_release_q_def)
   apply (clarsimp simp: valid_release_q_def)
  apply (subgoal_tac "distinct (thread # qs)")
   prefer 2
   apply (clarsimp simp: valid_sched_def valid_release_q_def)
  apply (subst release_queue_cong[where queue'="thread#qs"])
     apply (drule_tac time=time in sorted_eq_original_as_set)
     apply fastforce
    apply safe
  apply (subgoal_tac "distinct
        (thread # map fst (filter (\<lambda>(p, t'). t' \<le> time) (zip qs r)) @
         map fst (filter (\<lambda>(p, t'). \<not> t' \<le> time) (zip qs r)))")
   apply fastforce
  apply (drule_tac time=time in sorted_eq_original_as_set)
  apply (simp only: distinct.simps, safe)
  apply (simp only: distinct_append, intro conjI distinct_map_filter distinct_map_fst_zip; assumption?)
  apply (simp only: set_map)
  apply (simp add: disjoint_iff_not_equal)
  apply clarsimp
  apply (frule_tac a=aa and b=b and b'=ba and ys=r in distinct_zip_fun)
  by (simp+)

crunches sched_context_resume
for budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"
and not_cur_thread'[wp]: "\<lambda>s. P (not_cur_thread t s)"
  (wp: crunch_wps)

lemma postpone_valid_sched: (* sc_ptr is linked to a thread that is not in any queue *)
  "\<lbrace>valid_sched_except_blocked and
    (\<lambda>s. sc_tcb_sc_at (\<lambda>p. \<forall>tp. p = Some tp
      \<and> valid_blocked_except tp s \<and> st_tcb_at runnable tp s
      \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s
      \<and> scheduler_act_not tp s) sc_ptr s)\<rbrace>
    postpone sc_ptr \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched (* ? *)
            tcb_sched_action_dequeue_valid_blocked_except tcb_dequeue_not_queued
            tcb_sched_action_dequeue_valid_ready_qs)
  by (fastforce simp: valid_sched_def sc_tcb_sc_at_def obj_at_def
                    valid_blocked_def valid_blocked_except_def)

lemma postpone_valid_sched_tcb: (* sc_ptr is linked to a thread that is not in any queue *)
  "\<lbrace>valid_sched_except_blocked and
    (\<lambda>s. \<exists>tp. sc_tcb_sc_at (\<lambda>x. x = Some tp) sc_ptr s
      \<and> valid_blocked_except tp s \<and> st_tcb_at runnable tp s
      \<and> not_in_release_q tp s \<and> active_sc_tcb_at tp s
      \<and> scheduler_act_not tp s)\<rbrace>
    postpone sc_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched (* ? *)
            tcb_sched_action_dequeue_valid_blocked_except2 tcb_dequeue_not_queued
            tcb_sched_action_dequeue_valid_ready_qs)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma postpone_valid_sched':  (* sc_ptr is linked to a thread in a ready_q *)
  "\<lbrace>valid_sched and
    (\<lambda>s. sc_tcb_sc_at (\<lambda>p. \<forall>tp. p = Some tp
     \<and> (\<exists>d p. tp \<in> set (ready_queues s d p))
      \<and> not_in_release_q tp s
      \<and> scheduler_act_not tp s) sc_ptr s)\<rbrace>
    postpone sc_ptr \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (unfold postpone_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (wpsimp wp: tcb_release_enqueue_valid_sched (* ? *)
            tcb_sched_action_dequeue_valid_blocked_except tcb_dequeue_not_queued
            tcb_sched_action_dequeue_valid_ready_qs)
  by (fastforce simp: valid_sched_def sc_tcb_sc_at_def obj_at_def
                    valid_blocked_def valid_ready_qs_def)

lemma sched_context_resume_valid_sched:
  "\<lbrace>valid_sched_except_blocked and
    (\<lambda>s. sc_tcb_sc_at (\<lambda>p. \<forall>t. p = Some t
         \<and> scheduler_act_not t s
         \<and> bound_sc_tcb_at (\<lambda>s. s = Some sc_ptr) t s
         \<and> valid_blocked_except t s \<and> t \<noteq> idle_thread s) sc_ptr s)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: sched_context_resume_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp simp: when_def; rule conjI; clarsimp)
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (rule hoare_seq_ext[OF _ thread_get_sp])
   apply (clarsimp simp: get_tcb_queue_def)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ assert_sp])
    apply (wpsimp wp: postpone_valid_sched)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def pred_tcb_at_def is_schedulable_opt_def get_tcb_rev)
    apply (drule_tac x=tp in spec)
    apply (clarsimp simp: active_sc_tcb_at_defs)
  by (wpsimp, clarsimp simp: sc_tcb_sc_at_def obj_at_def pred_tcb_at_def valid_blocked_def
      valid_blocked_except_def valid_sched_def)+

lemma test_possible_switch_to_valid_sched:
  "\<lbrace>valid_sched and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)
    and (\<lambda>s. bound_sc_tcb_at bound target s \<and> not_in_release_q target s
      \<longrightarrow> budget_ready target s \<and> budget_sufficient target s)\<rbrace>
     test_possible_switch_to target \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding test_possible_switch_to_def gets_the_def
  apply (wpsimp wp: possible_switch_to_valid_sched' is_schedulable_wp)
  by (fastforce simp: valid_sched_def valid_blocked_except_def valid_blocked_def
                      is_schedulable_opt_def not_in_release_q_def active_sc_tcb_at_defs
                split: option.splits dest!: get_tcb_SomeD)


context DetSchedSchedule_AI begin

crunches arch_tcb_set_ipc_buffer,install_tcb_cap
for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
and simple_sched_action[wp]: "simple_sched_action :: det_state \<Rightarrow> _"
  (wp: crunch_wps check_cap_inv simp: crunch_simps)

lemma tc_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
      invoke_tcb (ThreadControl target slot fault_handler timeout_handler mcp priority croot vroot buffer sc)
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
(*
  unfolding split_def set_mcpriority_def
  by ((simp add: conj_comms, strengthen imp_consequent[where Q="x = None" for x], simp cong: conj_cong)
          | wp check_cap_inv thread_set_not_state_valid_sched hoare_vcg_all_lift gts_wp static_imp_wp
          | wpc | simp add: option_update_thread_def | rule reschedule_preserves_valid_sched
          | wp_once hoare_drop_imps )+
*)
  including no_pre
  apply (simp add: split_def set_mcpriority_def cong: option.case_cong)
  apply (rule hoare_vcg_precond_imp)
apply (wpsimp wp: check_cap_inv static_imp_wp)
apply (wpsimp wp: thread_set_not_state_valid_sched sched_context_unbind_tcb_valid_sched
                  static_imp_wp hoare_vcg_all_lift hoare_vcg_conj_lift
           | wp_once hoare_drop_imps | simp add: option_update_thread_def)+
(*   by (wp check_cap_inv thread_set_not_state_valid_sched hoare_vcg_all_lift gts_wp static_imp_wp
         | wpc | simp add: option_update_thread_def | rule reschedule_preserves_valid_shed
         | wp_once hoare_drop_imps )+*)
  sorry (* invoke_tcb TC *)


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
   apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked hoare_vcg_if_lift2
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

lemma refill_ready_tcb_simp0:
    "refill_ready_tcb t s = ({(True, s)}, False) \<longleftrightarrow>
       (\<exists>tcb scp sc n.
        r_time (refill_hd sc) \<le> cur_time s + kernelWCET_ticks \<and>
        sufficient_refills 0 (sc_refills sc) \<and>
        tcb_sched_context tcb = Some scp \<and> kheap s t = Some (TCB tcb) \<and>
        kheap s scp = Some (SchedContext sc n))"
  apply (rule iffI)
   apply (clarsimp simp: refill_ready_tcb_def get_tcb_obj_ref_def assert_opt_def thread_get_def
      gets_the_conv bind_assoc get_def split_def bind_def return_def refill_ready_def get_refills_def
      simpler_gets_def get_sched_context_def get_object_def assert_def refill_sufficient_def
      split: if_splits option.splits dest!: get_tcb_SomeD)
   apply (case_tac y; clarsimp simp: return_def)
  apply (clarsimp simp: refill_ready_tcb_def get_tcb_obj_ref_def assert_opt_def thread_get_def
      gets_the_conv bind_assoc get_def split_def bind_def return_def refill_ready_def get_refills_def
      simpler_gets_def get_sched_context_def get_object_def assert_def refill_sufficient_def
      split: if_splits option.splits dest!: get_tcb_SomeD)
  by (intro conjI allI impI; (fastforce simp: get_tcb_rev return_def dest!: get_tcb_SomeD))

lemma refill_ready_tcb_simp0':
    "refill_ready_tcb t s = ({(False, s)}, False) \<longleftrightarrow>
       (\<exists>tcb scp sc n.
        \<not>(r_time (refill_hd sc) \<le> cur_time s + kernelWCET_ticks \<and>
        sufficient_refills 0 (sc_refills sc)) \<and>
        tcb_sched_context tcb = Some scp \<and> kheap s t = Some (TCB tcb) \<and>
        kheap s scp = Some (SchedContext sc n))"
  apply (rule iffI)
   apply (clarsimp simp: refill_ready_tcb_def get_tcb_obj_ref_def assert_opt_def thread_get_def
      gets_the_conv bind_assoc get_def split_def bind_def return_def refill_ready_def get_refills_def
      simpler_gets_def get_sched_context_def get_object_def assert_def refill_sufficient_def
      split: if_splits option.splits dest!: get_tcb_SomeD)
   apply (case_tac y; clarsimp simp: return_def)
  apply (clarsimp simp: refill_ready_tcb_def get_tcb_obj_ref_def assert_opt_def thread_get_def
      gets_the_conv bind_assoc get_def split_def bind_def return_def refill_ready_def get_refills_def
      simpler_gets_def get_sched_context_def get_object_def assert_def refill_sufficient_def
      split: if_splits option.splits dest!: get_tcb_SomeD)
  apply (intro conjI allI impI; (fastforce simp: get_tcb_rev return_def dest!: get_tcb_SomeD))
  done

lemma refill_ready_tcb_simp[simp]:
    "\<lbrakk> tcb_sched_context tcb = Some scp; kheap s t = Some (TCB tcb);
        kheap s scp = Some (SchedContext sc n)\<rbrakk> \<Longrightarrow>
     refill_ready_tcb t s
      = ({(r_time (refill_hd sc) \<le> cur_time s + kernelWCET_ticks \<and>
           sufficient_refills 0 (sc_refills sc), s)}, False)"
  apply (case_tac "r_time (refill_hd sc) \<le> cur_time s + kernelWCET_ticks \<and>
                   sufficient_refills 0 (sc_refills sc)")
  apply (clarsimp simp: refill_ready_tcb_simp0 refill_ready_tcb_simp0')
  apply (simp only:)
  by (fastforce simp: refill_ready_tcb_simp0')+

(* FIXME maybe move *)
lemma fun_of_m_imp: "f s = ({(b, s')}, False) \<Longrightarrow> (fun_of_m f s = Some b)"
  by (clarsimp simp: fun_of_m_def the_equality)

lemma fun_of_m_iff: "(\<exists>s'. f s = ({(b, s')}, False)) \<longleftrightarrow> (fun_of_m f s = Some b)"
  by (fastforce simp: fun_of_m_def the_equality split: if_split_asm)+


lemma awaken_ready_qs_helper:
  "\<lbrace>valid_ready_qs and K (distinct queue) and
   (\<lambda>s. \<forall>target\<in>set queue. (st_tcb_at runnable target
and active_sc_tcb_at target and
     budget_ready target and
     budget_sufficient target) s)\<rbrace>
         mapM_x (\<lambda>t. do possible_switch_to t;
                        modify (reprogram_timer_update (\<lambda>_. True))
                     od) queue \<lbrace>\<lambda>_. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (induct queue; clarsimp simp: mapM_append_single mapM_x_Nil mapM_x_Cons bind_assoc)
  by (wpsimp wp: possible_switch_to_st_tcb_at hoare_vcg_ball_lift
                 possible_switch_to_valid_ready_qs)

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

lemma awaken_valid_sched_helper':
  "\<lbrace>valid_sched and K (distinct queue)
and (\<lambda>s. \<forall>target \<in> set queue. ((st_tcb_at runnable target
and active_sc_tcb_at target and not_in_release_q target and
     budget_ready target and not_cur_thread target and
     budget_sufficient target) s ))\<rbrace>
         mapM_x (\<lambda>t. do possible_switch_to t;
                        modify (reprogram_timer_update (\<lambda>_. True))
                     od) queue \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (induct queue; clarsimp simp: mapM_append_single mapM_x_Nil mapM_x_Cons bind_assoc)
  by (wpsimp wp: possible_switch_to_valid_sched hoare_vcg_ball_lift)

(* FIXME: Move *)
lemma distinct_takeWhle:
   "\<lbrakk>distinct ls; t \<in> set (takeWhile P ls)\<rbrakk>
    \<Longrightarrow> t \<notin> set (drop (length (takeWhile P ls)) ls)"
  apply (subst dropWhile_eq_drop[symmetric])
  apply (subgoal_tac "distinct ((takeWhile P ls) @ (dropWhile P ls))")
   apply (simp only: distinct_append, fastforce)
  apply fastforce
  done

(* FIXME: Move *)
lemma distinct_not_in_takeWhile:
   "\<lbrakk>distinct ls; t \<in> set ls; t \<notin> set (takeWhile P ls)\<rbrakk>
    \<Longrightarrow> t \<in> set (drop (length (takeWhile P ls)) ls)"
  apply (subst dropWhile_eq_drop[symmetric])
  apply (subgoal_tac "distinct ((takeWhile P ls) @ (dropWhile P ls))")
   apply (simp only: distinct_append, elim conjE)
  apply (subgoal_tac "set ls = set (takeWhile P ls) \<union> set (dropWhile P ls)")
  apply fastforce
apply (subst takeWhile_dropWhile_id[symmetric, of _ P])
apply (subst set_append, auto)
  done

(* FIXME: Move *)
lemma valid_rlq_distinct[intro!]: "valid_release_q s \<Longrightarrow> distinct (release_queue s)"
  by (clarsimp simp: valid_release_q_def)

(* FIXME: Move *)
lemma valid_sched_valid_release_q: "valid_sched s \<Longrightarrow> valid_release_q s"
  by (clarsimp simp: valid_sched_def)

(* FIXME: Move *)
lemma dropWhile_dropped_P:
  "\<lbrakk>x \<in> set queue; x \<notin> set (dropWhile P queue)\<rbrakk> \<Longrightarrow> P x"
  by (induction queue arbitrary: x; fastforce split: if_split_asm)

(* FIXME: Move *)
lemma takeWhile_taken_P:
  "x \<in> set (takeWhile P queue) \<Longrightarrow> P x"
  by (induction queue arbitrary: x; fastforce split: if_split_asm)

lemma awaken_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. not_in_release_q (idle_thread s) s)
   and (\<lambda>s. cur_thread s \<in> set (release_queue s) \<longrightarrow> \<not> budget_ready (cur_thread s) s)\<rbrace>
   awaken \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding awaken_def
  unfolding fun_of_m_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_valid_sched_helper simp: valid_sched_def)
  apply (subst dropWhile_eq_drop[symmetric])
  apply (intro conjI) prefer 3
        apply (clarsimp simp: valid_sched_def valid_release_q_def intro!: distinct_takeWhile)
       prefer 6
       apply clarsimp
       apply (frule distinct_takeWhle[rotated])
        apply clarsimp
       apply (clarsimp simp: not_in_release_q_def)
       apply (drule set_takeWhileD)
       apply (clarsimp simp: valid_release_q_def active_sc_tcb_at_defs dest!: valid_sched_valid_release_q)
       apply (drule_tac x=target in bspec, clarsimp)
       apply (clarsimp split: option.splits)
       apply (rename_tac y)
       apply (case_tac y; clarsimp simp: is_refill_ready_def is_refill_sufficient_def obj_at_def)
      apply (fastforce simp: valid_release_q_def dest!: set_dropWhileD)+
     apply (subst dropWhile_eq_drop[symmetric])
     apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def dest!: set_dropWhileD)
    defer
    apply (subst dropWhile_eq_drop[symmetric])
    apply (clarsimp simp: valid_blocked_except_set_def valid_blocked_def dest!: set_dropWhileD)+
    apply (case_tac "t \<in> set (release_queue s)")
     prefer 2
    (* t is not in release_queue from the beginning *)
     apply (drule_tac x=t in spec, clarsimp simp: not_in_release_q_def)
    (* t is/was in release_queue *)
    apply (drule (1) distinct_not_in_takeWhile[rotated])
     apply (clarsimp simp: valid_release_q_def)
    apply (clarsimp simp: not_in_release_q_def dropWhile_eq_drop[symmetric])
   apply (clarsimp dest!: set_takeWhileD
      simp: valid_release_q_def is_refill_ready_def active_sc_tcb_at_defs)
   apply (drule_tac x="cur_thread s" in bspec, simp)
   apply (clarsimp simp: etcb_defs split: option.splits, case_tac y; clarsimp)
  apply (clarsimp simp: not_in_release_q_def dest!: set_takeWhileD)
  done

crunches sc_and_timer
for valid_idle[wp]: "valid_idle::det_ext state \<Rightarrow> bool"
  (wp: hoare_drop_imps)

crunches awaken
for cur_tcb[wp]: cur_tcb
and budget_ready: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient: "\<lambda>s. P (budget_sufficient t s)"
and budget_ready_ct: "\<lambda>s. P (budget_ready (cur_thread s) s)"
and budget_sufficient_ct: "\<lambda>s. P (budget_sufficient (cur_thread s) s)"
  (wp: hoare_drop_imps mapM_x_wp')


context DetSchedSchedule_AI begin



lemma schedule_valid_sched:
  "\<lbrace>cur_tcb and valid_sched and valid_idle (*and cur_tcb and (\<lambda>s. \<not>in_release_queue (cur_thread s) s)*)\<rbrace>
     schedule \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_def
apply (rule hoare_pre)
apply (rule hoare_seq_ext[OF _ hoare_vcg_conj_lift[OF awaken_valid_sched
                                  hoare_vcg_conj_lift[OF awaken_valid_idle awaken_cur_tcb]]])
apply clarsimp
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (case_tac action; clarsimp simp: bind_assoc)
         (* resume_cur_thread *)
         apply wpsimp
        prefer 2
        (* choose new thread *)
        apply (case_tac ct_schedulable; clarsimp)
             (* ct schedulable *)
        apply (wpsimp wp: schedule_choose_new_thread_valid_sched tcb_sched_action_enqueue_valid_blocked
                   tcb_sched_enqueue_cur_ct_in_q split_del: if_split)
 apply (clarsimp simp: valid_sched_def is_schedulable_bool_def cur_tcb_def obj_at_def is_tcb
get_tcb_rev pred_tcb_at_def active_sc_tcb_at_def valid_blocked_def valid_blocked_except_def
split: option.splits)
      (* ct not schedulable *)
(*
subgoal
apply (wpsimp wp: schedule_choose_new_thread_valid_sched)
apply (clarsimp simp: valid_sched_def)
*)
 (* need lemmas for the case where ct is not schedulable? or is this false? *)

        (* switch_thread to candidate
        apply (rename_tac candidate)
        apply (case_tac ct_schedulable; clarsimp)
             (* ct schedulable *)


       (* switch_thread candidate *)
       apply (rename_tac candidate)
       apply (wp del: hoare_when_wp
                  add: set_scheduler_action_rct_valid_sched schedule_choose_new_thread_valid_sched)
                apply (rule hoare_vcg_conj_lift)
                 apply (rule_tac t=candidate in set_scheduler_action_cnt_valid_blocked')
                apply (wp tcb_sched_action_enqueue_valid_blocked tcb_sched_enqueue_ct_in_q enqueue_thread_queued)+
                 apply (wp schedule_choose_new_thread_valid_sched)+
                apply (rule hoare_vcg_conj_lift)
                 apply (rule_tac t=candidate in set_scheduler_action_cnt_valid_blocked')
               apply (wp tcb_sched_action_append_valid_blocked tcb_sched_append_ct_in_q
                         append_thread_queued set_scheduler_action_rct_switch_thread_valid_sched
                         guarded_switch_to_lift switch_to_thread_valid_sched
                         stt_activatable[simplified ct_in_state_def]
                         hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
                         switch_to_thread_sched_act_is_cur)+
           (* discard result of fastfail calculation *)
           apply (wpsimp wp: hoare_drop_imp)+
       apply (strengthen valid_blocked_valid_blocked_except)
       apply (wpsimp wp: tcb_sched_action_enqueue_valid_blocked tcb_sched_enqueue_cur_ct_in_q gts_wp
                 hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift awaken_valid_sched)
apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_2_def
         valid_blocked_def valid_blocked_except_def switch_in_cur_domain_def
     ct_not_in_q_def cong: conj_cong)
(*
  apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        switch_in_cur_domain_def)
  apply (safe ; (fastforce elim: st_tcb_at_opeqI
                 | fastforce simp: valid_sched_def valid_blocked_def valid_blocked_except_def
                                   valid_sched_action_def weak_valid_sched_action_def
                                   switch_in_cur_domain_def ct_in_q_def ct_not_in_q_def
                                   st_tcb_at_def obj_at_def)?)+*)
*)
sorry (* schedule_valid_sched *)

crunches cancel_ipc
for not_cur_thread[wp]: "not_cur_thread thread"
  (wp: hoare_drop_imps select_wp mapM_x_wp simp: unless_def if_fun_split)


lemma restart_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace> restart thread \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  including no_pre
  apply (simp add: restart_def | wp set_thread_state_runnable_valid_ready_qs
                                    set_thread_state_runnable_valid_sched_action
                                    set_thread_state_valid_blocked_except
                                    sts_st_tcb_at' cancel_ipc_simple2
                                    possible_switch_to_valid_sched)+
    apply (rule_tac Q="\<lambda>_. valid_sched and not_cur_thread thread and (\<lambda>s. thread \<noteq> idle_thread s)" in hoare_strengthen_post)
     apply wp
(*    apply (simp add: valid_sched_def)
   apply (simp add: if_fun_split)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: get_thread_state_def thread_get_def)
    apply wp

   apply (simp add: get_thread_state_def | wp hoare_drop_imps)+
  apply (clarsimp simp: not_cur_thread_def valid_sched_def valid_sched_action_def
                        is_activatable_def)
  apply (drule_tac test="\<lambda>ts. \<not> activatable ts" in st_tcb_at_get_lift)
*)
   apply (simp add: valid_sched_def)
(*  apply (simp add: if_fun_split)
  apply (rule hoare_conjI)
   apply (simp add: get_thread_state_def thread_get_def)
   apply wp
   apply (clarsimp simp: not_cur_thread_def valid_sched_def valid_sched_action_def
                         is_activatable_def)
   apply (drule_tac test="\<lambda>ts. \<not> activatable ts" in st_tcb_at_get_lift)
    apply simp
   apply (simp only: st_tcb_at_not)
   apply simp
  apply (simp add: get_thread_state_def | wp hoare_drop_imps)+
  done*)
sorry (* restart *)

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
  "\<lbrace>invs and valid_sched and simple_sched_action and tcb_inv_wf ti\<rbrace> invoke_tcb ti \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases ti, simp_all only:)
         defer 5
         apply (wp mapM_x_wp tc_valid_sched suspend_valid_sched
                | simp
                | rule subset_refl
                | rule reschedule_preserves_valid_shed
                | clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap
                | intro impI conjI)+
        apply (rename_tac option)
        apply (case_tac option)
        apply (wp mapM_x_wp suspend_valid_sched | simp | rule subset_refl | clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap | intro impI conjI)+
  done

end

crunch valid_sched[wp]: store_word_offs "valid_sched::det_state \<Rightarrow> _"

crunch exst[wp]: set_mrs, as_user "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

crunch ct_not_in_q[wp]: as_user ct_not_in_q
  (wp: ct_not_in_q_lift)

lemmas gts_drop_imp = hoare_drop_imp[where f="get_thread_state p" for p]

(* FIXME: Move *)
lemma valid_blocked_except_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and f: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s)\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>valid_blocked_except thread\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked_except thread\<rbrace>"
  apply (rule hoare_pre)
   apply (wps c e d f)
   apply (simp add: valid_blocked_except_def)
   apply (wp static_imp_wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift)
   apply (rule hoare_convert_imp)
    apply (rule typ_at_st_tcb_at_lift)
     apply (wp a b t)+
  apply (simp add: valid_blocked_except_def)
  done

lemma as_user_valid_blocked_except[wp]:
 "\<lbrace>valid_blocked_except thread\<rbrace> as_user param_a param_b \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp wp: valid_blocked_except_lift)

(* FIXME: Move *)
lemma set_simple_ko_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_simple_ko f ptr ntfn \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps valid_sched_action_lift | simp add: set_simple_ko_def)+

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

crunches tcb_release_enqueue
  for cur_thread_is_activatable[wp]: "\<lambda>s. is_activatable (cur_thread s) s"
  and switch_in_cur_domain[wp]: switch_in_cur_domain
  (wp: crunch_wps)

(* FIXME move *)
lemma length_eq_pair_in_set_zip:
  "length qs = length r \<Longrightarrow> x \<in> set qs \<Longrightarrow> \<exists>b. (x, b) \<in> set (zip qs r)"
  apply (induct qs arbitrary: r; simp)
  apply (safe; case_tac r; fastforce)
  done

lemma tcb_release_enqueue_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
   tcb_release_enqueue tcb_ptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. weak_valid_sched_action_2 (scheduler_action s) (kheap s) (tcb_ptr # qs)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: release_queue_cong')
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

lemma sched_context_resume_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. \<forall>y. sc_tcb_sc_at ((=) (Some y)) sc_ptr s \<longrightarrow> scheduler_act_not y s)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace> "
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_sched_action thread_get_wp is_schedulable_wp)
  apply (fastforce simp: obj_at_def is_schedulable_opt_def
                 dest!: get_tcb_SomeD split: option.splits)
  done

(* FIXME: move *)
lemma is_round_robin_wp:
  "\<lbrace>\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) x s \<longrightarrow> P (sc_period sc = 0) s\<rbrace> is_round_robin x \<lbrace>\<lambda>r. P r\<rbrace>"
  by (wpsimp simp: is_round_robin_def)

lemma tcb_release_enqueue_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q\<rbrace>
     tcb_release_enqueue tcb_ptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding tcb_release_enqueue_def
  by (wpsimp wp: mapM_wp')

lemma postpone_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q\<rbrace>
     postpone xa
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp:get_sc_obj_ref_wp)

lemma sched_context_resume_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q\<rbrace>
     sched_context_resume xa
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: thread_get_wp is_schedulable_wp)
  apply (fastforce simp: obj_at_def is_schedulable_opt_def
                  split: option.splits dest!: get_tcb_SomeD)
  done

lemma r_time_hd_refills_merge_prefix:
  "r_time (hd (refills_merge_prefix (a # l))) = r_time a"
  by (induct l arbitrary: a;
      clarsimp simp: merge_refill_def)

lemma refill_unblock_check_budget_ready[wp]:
  "\<lbrace>budget_ready x1\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>xc s. budget_ready x1 s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp )
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_refill_ready_def)
  apply (intro conjI impI, fastforce)
  apply (clarsimp simp: r_time_hd_refills_merge_prefix)
  apply (rule_tac x=scp in exI; clarsimp)
  apply (rule cur_time_assumption)
  done

lemma refill_unblock_check_budget_sufficient[wp]:
  "\<lbrace>budget_sufficient x1\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>xc s. budget_sufficient x1 s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp )
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_refill_sufficient_def
                        sufficient_refills_def refills_capacity_def)
  apply fastforce
  done

lemma refill_unblock_check_ct_not_in_q[wp]:
  "\<lbrace> ct_not_in_q\<rbrace>
     refill_unblock_check xa
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)

crunch ready_queues[wp]: refill_unblock_check "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps)

crunch release_queue[wp]: refill_unblock_check "\<lambda>s. P (release_queue s)"
  (wp: crunch_wps)

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

lemma refill_unblock_check_etcb_at:
  "\<lbrace> etcb_at P x\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r. etcb_at P x\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  by (clarsimp simp: etcb_at'_def etcbs_of'_def)

lemma refill_unblock_check_active_sc_tcb_at:
  "\<lbrace> active_sc_tcb_at x\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace> \<lambda>r. active_sc_tcb_at x\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  by (fastforce simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                        test_sc_refill_max_def)

lemma refill_unblock_check_valid_ready_qs:
  "\<lbrace> valid_ready_qs\<rbrace>
     refill_unblock_check xa
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: valid_ready_qs_def is_etcb_at_etcbs_of_tcb_at)
  apply (wpsimp simp: Ball_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_etcb_at
                      refill_unblock_check_active_sc_tcb_at)
  done

lemma refill_unblock_check_valid_release_q:
  "\<lbrace>valid_release_q\<rbrace> refill_unblock_check xa \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (clarsimp simp: valid_release_q_def)
  apply (wpsimp simp: Ball_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_active_sc_tcb_at)
  done

lemma refill_unblock_check_st_tcb_at:
  "\<lbrace>\<lambda>s. st_tcb_at P (cur_thread s) s\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>rv s. st_tcb_at P (cur_thread s) s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma refill_unblock_check_valid_blocked_except:
  "\<lbrace>valid_blocked_except S\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>rv. valid_blocked_except S\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
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

lemma refill_unblock_check_in_cur_domain:
  "\<lbrace>in_cur_domain t\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>rv. in_cur_domain t\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: in_cur_domain_def etcb_at'_def etcbs_of'_def)
  done

lemma refill_unblock_check_in_cur_domain_cur_thread:
  "\<lbrace>\<lambda>s. in_cur_domain (cur_thread s) s\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>rv s. in_cur_domain (cur_thread s) s\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: in_cur_domain_def etcb_at'_def etcbs_of'_def)
  done

crunch scheduler_action[wp]: refill_unblock_check "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma refill_unblock_check_valid_sched_action:
  "\<lbrace>valid_sched_action\<rbrace> refill_unblock_check xa \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (clarsimp simp: is_activatable_def weak_valid_sched_action_def switch_in_cur_domain_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_active_sc_tcb_at
                    refill_unblock_check_st_tcb_at refill_unblock_check_in_cur_domain)
  done

lemma refill_unblock_check_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace> refill_unblock_check xa \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  unfolding ct_in_cur_domain_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'' refill_unblock_check_active_sc_tcb_at
                    refill_unblock_check_st_tcb_at refill_unblock_check_in_cur_domain refill_unblock_check_it_ct
                    refill_unblock_check_in_cur_domain_cur_thread hoare_vcg_disj_lift)
  done

lemma maybe_donate_sc_ct_not_in_q:
  "\<lbrace> ct_not_in_q and (\<lambda>s. tcb_ptr \<noteq> cur_thread s)\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

crunch valid_ready_qs[wp]: tcb_release_enqueue valid_ready_qs
  (wp: crunch_wps)

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

lemma not_in_release_q_set_lift:
 "set A = set B \<Longrightarrow> not_in_release_q_2 A t = not_in_release_q_2 B t"
  by (clarsimp simp: not_in_release_q_2_def in_queue_2_def)

lemma distinct_shuffle_left:
  "distinct (A @ x # B) = distinct (x # A @ B)"
  by fastforce

lemma tcb_release_enqueue_valid_release_q:
  "\<lbrace> valid_release_q and st_tcb_at runnable tcb_ptr
     and active_sc_tcb_at tcb_ptr and not_in_release_q tcb_ptr\<rbrace>
     tcb_release_enqueue tcb_ptr
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: tcb_release_enqueue_def assert_opt_def)
  apply (rule hoare_seq_ext[OF _ get_sc_time_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv s. valid_release_q_2 (tcb_ptr # qs) (kheap s)
           \<and> length qs = length rv" in hoare_strengthen_post)
    apply (wpsimp wp: mapM_wp_inv_length cong: release_queue_cong')
   prefer 2
   apply (clarsimp simp: valid_release_q_def  not_in_release_q_def
                    pred_tcb_at_def obj_at_def split: option.splits)
  apply (subgoal_tac "distinct (tcb_ptr # qs)")
   prefer 2
   apply (clarsimp simp: valid_release_q_def)
  apply (subst release_queue_cong2[where queue'="tcb_ptr # qs"];
         (solves \<open>simp\<close>)?)
   apply (subst tcb_release_enqueue_set_ident; simp)
  apply (subst distinct_shuffle_left)
  apply clarsimp
  apply (intro conjI distinct_map_filter distinct_map_fst_zip; assumption?)
    apply (clarsimp simp: image_def dest!: in_set_zip1)
   apply (clarsimp simp: image_def dest!: in_set_zip1)
  apply (simp add: disjoint_iff_not_equal)
  apply clarsimp
  apply (frule_tac a=aa and b=b and b'=ba and ys=r in distinct_zip_fun)
  by (simp+)

lemma postpone_valid_ready_qs:
  "\<lbrace> valid_ready_qs \<rbrace>
     postpone xa
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  by (wpsimp wp: tcb_sched_action_dequeue_valid_ready_qs get_sc_obj_ref_wp)

lemma postpone_valid_release_q:
  "\<lbrace> valid_release_q and (\<lambda>s. \<forall>sc n y. ko_at (SchedContext sc n) xa s \<longrightarrow> sc_tcb sc = Some y \<longrightarrow>
       st_tcb_at runnable y s \<and> active_sc_tcb_at y s \<and> not_in_release_q y s)\<rbrace>
     postpone xa
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding postpone_def
  apply (wpsimp wp: tcb_release_enqueue_valid_release_q  get_sc_obj_ref_wp)
  by (fastforce)

lemma thread_get_wp':
  "\<lbrace>\<lambda>s. \<forall>tcb. obj_at (\<lambda>ko. ko = TCB tcb) ptr s \<longrightarrow> P (f tcb) s\<rbrace>
    thread_get f ptr
   \<lbrace>P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done

lemma sched_context_resume_valid_ready_qs:
  "\<lbrace> valid_ready_qs \<rbrace>
     sched_context_resume xa
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_valid_ready_qs is_schedulable_wp
           simp: thread_get_def)

lemma sched_context_resume_valid_valid_release_q:
  "\<lbrace> valid_release_q and (\<lambda>s. \<forall>y. sc_tcb_sc_at ((=) (Some y)) xa s \<longrightarrow>
       st_tcb_at runnable y s \<and> not_in_release_q y s \<and> bound_sc_tcb_at ((=) (Some xa)) y s)\<rbrace>
     sched_context_resume xa
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: postpone_valid_release_q is_schedulable_wp
              simp: thread_get_def)
  apply (intro conjI)
    prefer 3
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply (fastforce simp: obj_at_def active_sc_tcb_at_def pred_tcb_at_def test_sc_refill_max_def
                         sc_at_pred_n_def
                  dest!: get_tcb_SomeD
                 split: option.splits)
  done

lemma maybe_donate_sc_valid_ready_qs:
  "\<lbrace> valid_ready_qs and scheduler_act_not tcb_ptr and not_queued tcb_ptr \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_ready_qs :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_valid_ready_qs refill_unblock_check_valid_ready_qs
      hoare_vcg_if_lift2 maybeM_wp simp: get_sc_obj_ref_def obj_at_def)
   apply wpsimp
  done

lemma refill_unblock_check_ko_at_SchedContext:
  "\<lbrace>\<lambda>s. P (sc_tcb_sc_at ((=) (Some ya)) xa s)\<rbrace>
    refill_unblock_check xa
   \<lbrace>\<lambda>rv s. P (sc_tcb_sc_at ((=) (Some ya)) xa s)\<rbrace>"
   unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma maybe_donate_sc_valid_release_q_helper:
  "\<lbrace>not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr and sc_tcb_sc_at ((=) None) xa\<rbrace>
   sched_context_donate xa tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) xa s \<longrightarrow>
               st_tcb_at runnable x s \<and> not_in_release_q x s \<and> bound_sc_tcb_at ((=) (Some xa)) x s\<rbrace>"
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

lemma maybe_donate_sc_valid_release_q:
  "\<lbrace> valid_release_q and not_in_release_q tcb_ptr and st_tcb_at runnable tcb_ptr\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. valid_release_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: sched_context_resume_valid_valid_release_q refill_unblock_check_valid_release_q
                     hoare_vcg_all_lift hoare_vcg_imp_lift' refill_unblock_check_ko_at_SchedContext)
     apply (wpsimp wp: sched_context_donate_valid_release_q maybe_donate_sc_valid_release_q_helper)
    apply (wpsimp simp: get_sc_obj_ref_def)
   apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  apply wpsimp
  done

lemma maybe_donate_sc_valid_sched_action_helper:
  "\<lbrace>scheduler_act_not tcb_ptr and sc_tcb_sc_at ((=) None) xa\<rbrace>
   sched_context_donate xa tcb_ptr
   \<lbrace>\<lambda>rv s. \<forall>x. sc_tcb_sc_at ((=) (Some x)) xa s \<longrightarrow> scheduler_act_not x s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def
                  wp: set_object_wp update_sched_context_wp)
        apply (rule hoare_pre_cont)
       apply (wpsimp)+
   apply (wpsimp simp: get_sc_obj_ref_def)
  apply (clarsimp simp: obj_at_def sc_at_pred_n_def)
  done

lemma maybe_donate_sc_valid_sched_action:
  "\<lbrace> valid_sched_action and scheduler_act_not tcb_ptr\<rbrace>
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

crunch ct_in_cur_domain[wp]: tcb_release_enqueue ct_in_cur_domain
  (wp: crunch_wps)

lemma postpone_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace> postpone xa
          \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
    unfolding postpone_def
  apply (wpsimp wp: get_sc_obj_ref_wp)
  done

lemma sched_context_resume_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain\<rbrace> sched_context_resume xa
          \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
    unfolding sched_context_resume_def
  by (wpsimp wp: postpone_ct_in_cur_domain is_schedulable_wp
           simp: thread_get_def)

lemma maybe_donate_sc_ct_in_cur_domain:
  "\<lbrace> ct_in_cur_domain \<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: sched_context_resume_ct_in_cur_domain refill_unblock_check_ct_in_cur_domain
                    get_sk_obj_ref_wp get_tcb_obj_ref_wp)

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

lemma not_queued_tcb_sched_dequeue_wp:
  "\<lbrace>Q and not_queued tcb_ptr\<rbrace>
   tcb_sched_action tcb_sched_dequeue tcb_ptr
   \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding tcb_sched_action_def
  apply (wpsimp)
  apply (clarsimp simp: obj_at_def tcb_sched_dequeue_def)
  apply (subst filter_True, clarsimp simp: not_queued_def)
  apply (subgoal_tac "(\<lambda>t' p.
                     if t' = tcb_domain tcb \<and> p = tcb_priority tcb
                     then ready_queues s (tcb_domain tcb) (tcb_priority tcb)
                     else ready_queues s t' p) = (\<lambda>t' p. ready_queues s t' p)")
   apply simp
  apply fastforce
  done

lemma tcb_sched_dequeue_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set S and not_queued tcb_ptr\<rbrace>
   tcb_sched_action tcb_sched_dequeue tcb_ptr
   \<lbrace>\<lambda>_. valid_blocked_except_set S\<rbrace>"
  by (rule not_queued_tcb_sched_dequeue_wp)

(* FIXME: move *)
lemma valid_blocked_except_set_subset:
  "T \<subseteq> S \<Longrightarrow>
   valid_blocked_except_set T s \<Longrightarrow>
   valid_blocked_except_set S s"
  by (fastforce simp: valid_blocked_except_set_def)

lemma postpone_valid_blocked_except_set:
  "\<lbrace> valid_blocked_except_set {tcb_ptr} and
     (\<lambda>s. \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s)\<rbrace>
      postpone sc_ptr
   \<lbrace> \<lambda>_. valid_blocked_except_set {tcb_ptr} \<rbrace>"
    unfolding postpone_def
  apply (wpsimp wp: is_schedulable_wp tcb_release_enqueue_valid_blocked_except_set
                    tcb_sched_dequeue_valid_blocked_except_set get_sc_obj_ref_wp
              simp: thread_get_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  apply (fastforce elim: valid_blocked_except_set_subset[rotated])
  done

lemma sched_context_resume_valid_blocked_except_set:
  "\<lbrace>valid_blocked_except_set {tcb_ptr} and
    (\<lambda>s.  \<forall>t. sc_tcb_sc_at (\<lambda>p. p = Some t) sc_ptr s \<longrightarrow> not_queued t s)\<rbrace>
   sched_context_resume sc_ptr
   \<lbrace>\<lambda>_. valid_blocked_except_set {tcb_ptr} \<rbrace>"
    unfolding sched_context_resume_def
  by (wpsimp wp: postpone_valid_blocked_except_set is_schedulable_wp
           simp: thread_get_def)

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
   \<lbrace> \<lambda>_. valid_blocked_except_set {tcb_ptr} \<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (wpsimp wp: sched_context_resume_valid_blocked_except_set
                    refill_unblock_check_valid_blocked_except
                    not_queued_refill_unblock_check not_queued_sched_context_donate
                    sched_context_donate_valid_blocked_except_set
                    get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

crunches maybe_donate_sc
for not_cur_thread[wp]: "not_cur_thread t"
and etcbs[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: hoare_drop_imp crunch_wps ignore: set_tcb_obj_ref)

lemma possible_switch_to_bound_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
     possible_switch_to a
   \<lbrace>\<lambda>ya. bound_sc_tcb_at P t\<rbrace>"
  unfolding possible_switch_to_def
  by (wpsimp wp: reschedule_required_pred_tcb_at
           simp: get_tcb_obj_ref_def thread_get_def)

(* FIXME: Move *)
definition
  ntfn_sc_ntfn_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "ntfn_sc_ntfn_at P \<equiv> obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> P (ntfn_sc ntfn))"

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
  apply (wp sts_st_tcb_at' possible_switch_to_valid_sched'
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

lemma cancel_badged_sends_filterM_active_sc_tcb_at[wp]:
   "\<lbrace>active_sc_tcb_at t\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp sts_st_tcb_at' | simp)+
  done

lemma cancel_badged_sends_filterM_st_tcb_at[wp]:
   "\<lbrace>st_tcb_at runnable t\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  by (wpsimp wp: set_thread_state_st_tcb_at hoare_drop_imps | simp)+

lemma cancel_badged_sends_filterM_bound_sc_tcb_at[wp]:
   "\<lbrace>bound_sc_tcb_at P t\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  by (wpsimp wp: set_thread_state_st_tcb_at hoare_drop_imps possible_switch_to_bound_sc_tcb_at)

lemma cancel_badged_sends_filterM_weak_valid_sched_action[wp]:
   "\<lbrace>weak_valid_sched_action
     and (\<lambda>s. \<forall>x\<in> (set xs). bound_sc_tcb_at (\<lambda>sc. sc = None) x s \<or> active_sc_tcb_at x s)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. weak_valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply wpsimp
  apply (clarsimp simp: filterM_append)
  apply (wpsimp wp: set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
       hoare_vcg_conj_lift hoare_vcg_disj_lift hoare_drop_imps cong: conj_cong)
   apply simp+
  done

lemma cancel_badged_sends_filterM_ct_in_cur_domain[wp]:
   "\<lbrace>ct_in_cur_domain\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp | simp)+
  done

lemma cancel_badged_sends_filterM_valid_idle_etcb[wp]:
  notes valid_idle_etcb_lift[wp del]
  shows
   "\<lbrace>valid_idle_etcb\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_idle_etcb\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp  | simp | wp valid_idle_etcb_lift)+
  done

lemma cancel_badged_sends_filterM_valid_ready_qs[wp]:
   "\<lbrace>valid_ready_qs and
     (\<lambda>s. \<forall>t\<in> set xs. bound_sc_tcb_at (\<lambda>sc. sc = None) t s \<or>
                      active_sc_tcb_at t s \<and> budget_ready t s \<and> budget_sufficient t s)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (induct xs)
   apply wpsimp
  apply (clarsimp simp: bind_assoc)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: possible_switch_to_valid_ready_qs sts_st_tcb_at'
                    set_thread_state_runnable_valid_ready_qs hoare_vcg_all_lift
                    static_imp_wp hoare_vcg_ball_lift hoare_vcg_disj_lift
                    possible_switch_to_bound_sc_tcb_at
              cong: conj_cong imp_cong)
  apply fastforce
  done

lemma cancel_badged_sends_filterM_valid_release_q[wp]:
   "\<lbrace>valid_release_q\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append bind_assoc)
  by (wpsimp wp: set_thread_state_runnable_valid_release_q hoare_drop_imps)

lemma reschedule_required_valid_sched':
  "\<lbrace>valid_ready_qs and valid_release_q and weak_valid_sched_action
    and valid_blocked and valid_idle_etcb\<rbrace>
   reschedule_required
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+

definition is_BlockedOnSend where
  "is_BlockedOnSend t \<equiv> case t of BlockedOnSend _ _ \<Rightarrow> True | _ \<Rightarrow> False"

lemma choose_new_thread_blocked_except_simple:
  "\<lbrace>valid_blocked_except_set {t} and simple_sched_action\<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>_. valid_blocked_except_set {t}\<rbrace>"
  unfolding set_scheduler_action_def simple_sched_action_def
  apply (wpsimp)
  by (case_tac "scheduler_action s"; simp add: valid_blocked_except_def valid_blocked_def)

lemmas bound_sc_tcb_at_def = pred_tcb_at_def

lemma runnable_def':
  "runnable st = (st = Restart \<or> st = Running)"
  by (cases st; simp)

lemma choose_new_thread_blocked_except_switch:
  "\<lbrace>valid_blocked_except_set {t} and
  ((\<lambda>s:: det_state. scheduler_action s = switch_thread t' \<and>
         ((~ not_queued t' s) \<or> \<not> (is_schedulable_opt t' (in_release_queue t' s) s = Some True))))\<rbrace>
   set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_blocked_except_set {t}\<rbrace>"
  unfolding set_scheduler_action_def simple_sched_action_def
  apply (wpsimp)
  apply (simp add: valid_blocked_except_def valid_blocked_def is_schedulable_opt_def)
  apply (intro allI impI)
  apply (case_tac "ta = t'")
    (* ta = t' *)
   apply simp
   apply (split option.splits; simp add: get_tcb_def)
    apply (split option.splits; simp?)
     apply (intro disjI2; simp add: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def)
    apply (case_tac "x2"; simp add: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def)
   apply (split option.splits; simp?)
   apply (case_tac "x2a"; simp)
   apply (case_tac "tcb_sched_context x2"; simp)
    apply (intro disjI2; simp add: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def)
   apply (case_tac "runnable (tcb_state x2)"; simp)
    apply (case_tac "test_sc_refill_max a s"; simp)
     apply (simp add: in_release_queue_def not_in_release_q_def)
    apply (intro disjI2; simp add: active_sc_tcb_at_def bound_sc_tcb_at_def obj_at_def)
   apply (intro disjI1; simp add: st_tcb_at_def obj_at_def runnable_def')
    (* ta \<noteq> t' *)
  apply blast
 done

lemma tcb_sched_enqueue_queued[wp]:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_enqueue x2 \<lbrace>\<lambda>rv s. (\<not> not_queued x2 s)\<rbrace>"
  unfolding tcb_sched_action_def tcb_sched_enqueue_def
  apply wpsimp
  apply (clarsimp simp: not_queued_def obj_at_def)
  apply fastforce
  done

lemma tcb_sched_enqueue_increase:
  "t \<in> set S \<Longrightarrow> t \<in> set (tcb_sched_enqueue x S)"
  by (clarsimp simp: tcb_sched_enqueue_def)

lemma reschedule_required_valid_blocked_except':
  "\<lbrace>valid_blocked_except t\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_blocked_except t :: det_state \<Rightarrow> bool\<rbrace>"
  unfolding reschedule_required_def
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
    apply (wpsimp wp: choose_new_thread_blocked_except_simple)
   apply (wpsimp wp: choose_new_thread_blocked_except_simple)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (wpsimp)
    apply (rule_tac t'="x2" in choose_new_thread_blocked_except_switch)
   apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: is_schedulable_wp)+
  apply (clarsimp simp: is_schedulable_opt_def get_tcb_def split: option.splits)
  apply (clarsimp simp: valid_blocked_except_set_def)
  apply (intro conjI allI impI)
   apply (subgoal_tac "not_queued_2 (ready_queues s) ta")
    apply blast
   apply (clarsimp simp: not_queued_def)
   apply (subgoal_tac "ta \<in> set (if d = tcb_domain x2b \<and> p = tcb_priority x2b
                                 then tcb_sched_enqueue x2 (ready_queues s (tcb_domain x2b)
                                                                           (tcb_priority x2b))
                                 else ready_queues s d p)")
    apply fastforce
   apply (case_tac "d = tcb_domain x2b \<and> p = tcb_priority x2b")
    apply simp
    apply (rule tcb_sched_enqueue_increase; simp)
   apply (simp only: if_False)
  apply (simp add: not_queued_def tcb_sched_enqueue_def)
  apply fastforce
  done

lemma switch_thread_valid_blocked_except:
  "\<lbrace>valid_blocked_except target and (\<lambda>s. \<forall>t. scheduler_action s \<noteq> switch_thread t)\<rbrace>
     set_scheduler_action $ switch_thread target
   \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_scheduler_action_def
  apply (wpsimp)
  by (simp add: valid_blocked_except_def valid_blocked_def)

lemma tcb_sched_enqueue_valid_blocked_except:
  "\<lbrace>valid_blocked_except target\<rbrace>
     tcb_sched_action tcb_sched_enqueue target
   \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  unfolding tcb_sched_action_def tcb_sched_enqueue_def
  apply (wpsimp)
  apply (intro conjI impI allI)
  apply (simp add: valid_blocked_except_def valid_blocked_def not_queued_def)
  apply blast
  apply (simp add: valid_blocked_except_def valid_blocked_def not_queued_def)
  by (metis not_in_release_q_def)

lemma possible_switch_to_valid_blocked_strong:
  "\<lbrace>valid_blocked_except target \<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_blocked::det_state \<Rightarrow> _\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: tcb_sched_enqueue_valid_blocked_except
                    reschedule_required_valid_blocked_except'
                    switch_thread_valid_blocked_except
              simp: get_tcb_obj_ref_def thread_get_def)
  apply (intro allI impI conjI)
    apply fastforce
   apply (simp only: valid_blocked_except_set_def valid_blocked_def)
   apply (intro allI)
   apply (case_tac "t = target"; simp)
   apply (subgoal_tac "\<not> active_sc_tcb_at target s")
    apply fastforce
   apply (fastforce simp: get_tcb_def active_sc_tcb_at_def pred_tcb_at_def obj_at_def)[1]
  apply (simp only: valid_blocked_except_set_def valid_blocked_def)
  apply (intro allI)
  apply (case_tac "t = target"; simp)
  apply (fastforce simp: in_release_queue_def not_in_release_q_def)
  done

lemma cancel_badged_sends_filterM_valid_blocked[wp]:
   "\<lbrace>valid_blocked and K (distinct xs)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct xs)
   apply wpsimp
  apply (clarsimp simp: bind_assoc)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: possible_switch_to_valid_blocked_strong
                          set_thread_state_valid_blocked_except
              simp: ball_conj_distrib
              cong: conj_cong imp_cong)
  done

lemma cancel_badged_sends_valid_sched:
  "\<lbrace>valid_sched and valid_ep_q and
    (\<lambda>s. \<forall>x2. kheap s epptr = Some (Endpoint (SendEP x2)) \<longrightarrow> distinct x2)\<rbrace>
     cancel_badged_sends epptr badge
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp)
    defer 2
    apply (wpsimp+)[2]
  apply (wpsimp wp: hoare_drop_imps reschedule_required_valid_sched' hoare_vcg_conj_lift
                    hoare_vcg_ball_lift hoare_vcg_disj_lift cong: conj_cong)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def obj_at_def valid_ep_q_def)
  apply (drule_tac x=epptr in spec)
  apply (fastforce simp: pred_tcb_at_eq_commute)
  done

context DetSchedSchedule_AI begin

lemma cap_revoke_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
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
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma thread_set_st_tcb_at:
  "(\<And>x. P (tcb_state (f x)))
  \<Longrightarrow> \<lbrace>\<top>\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. st_tcb_at P tptr\<rbrace>"
  apply (simp add: thread_set_def set_object_def, wp)
  apply (clarsimp simp: valid_idle_def st_tcb_at_def obj_at_def)
  done

crunch valid_sched[wp]: cap_move "valid_sched :: det_state \<Rightarrow> _"

context DetSchedSchedule_AI begin

(* FIXME: move *)
lemma valid_objs_SendEP_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s xa = Some (Endpoint (SendEP x2)))
   \<Longrightarrow> distinct x2"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ep_def)
  done

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

end

crunches sched_context_update_consumed,set_extra_badge
for valid_sched[wp]:  "valid_sched::det_state \<Rightarrow> _"
and not_queued[wp]: "not_queued t::det_state \<Rightarrow> _"
and not_in_release_q[wp]: "not_in_release_q t::det_state \<Rightarrow> _"
and active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"
  (wp: valid_sched_lift)

crunch scheduler_act[wp]: set_extra_badge,cap_insert "\<lambda>s :: det_state. P (scheduler_action s)" (wp: crunch_wps)

lemma transfer_caps_lemmas[wp]:
  "\<lbrace>valid_sched\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>not_queued t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>not_in_release_q t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. not_in_release_q t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>active_sc_tcb_at t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>budget_ready t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. budget_ready t::det_state \<Rightarrow> _\<rbrace>"
  "\<lbrace>budget_sufficient t\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. budget_sufficient t::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+
  done

lemma possible_switch_to_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and K(target \<noteq> t)\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  by (wpsimp simp: set_scheduler_action_def get_tcb_obj_ref_def thread_get_def
     wp: tcb_sched_action_enqueue_not_queued reschedule_required_not_queued hoare_vcg_if_lift2
        split_del: if_split)

crunches unbind_reply_in_ts,no_reply_in_ts
for valid_ready_qs[wp]: valid_ready_qs
and not_queued[wp]: "not_queued t"
and ct_not_in_q[wp]: ct_not_in_q
and scheduler_act_not[wp]: "scheduler_act_not t"
and test_sc_refill_max[wp]: "test_sc_refill_max scp::det_state \<Rightarrow> _"
and is_refill_ready[wp]: "is_refill_ready scp::det_state \<Rightarrow> _"
and is_refill_sufficient[wp]: "is_refill_sufficient scp 0::det_state \<Rightarrow> _"
and active_sc_tcb_at[wp]: "active_sc_tcb_at t::det_state \<Rightarrow> _"
and budget_ready[wp]: "budget_ready t::det_state \<Rightarrow> _"
and budget_sufficient[wp]: "budget_sufficient t::det_state \<Rightarrow> _"
  (ignore: set_object wp: set_thread_state_not_queued_valid_ready_qs)

lemma reply_push_scheduler_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. scheduler_act_not t::det_state \<Rightarrow> _\<rbrace>"
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

lemma thread_set_fault_ct_active_wp:
  "\<lbrace> ct_active \<rbrace> thread_set (tcb_fault_update u) t \<lbrace>\<lambda>rv. ct_active::det_state \<Rightarrow> _ \<rbrace>"
  by (wpsimp wp: ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            simp: thread_set_def)

crunch scheduler_act[wp]: do_ipc_transfer "\<lambda>s :: det_state. P (scheduler_action s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

crunches do_ipc_transfer, handle_fault_reply
for valid_sched[wp]: "valid_sched::det_state \<Rightarrow> _"
and not_queued[wp]: "not_queued t::det_state \<Rightarrow> _"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres )

lemma send_ipc_not_queued_for_timeout:
  "\<lbrace>not_queued t and scheduler_act_not t and
    (\<lambda>s. \<forall>xa xb. kheap s (cap_ep_ptr cap) = Some (Endpoint (RecvEP (xa # xb))) \<longrightarrow> xa \<noteq> t)\<rbrace>
      send_ipc True False (cap_ep_badge cap) True
                 canDonate tptr (cap_ep_ptr cap) \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  apply (wpsimp wp: hoare_drop_imp get_simple_ko_wp split_del: if_split )
  by (clarsimp simp: ex_nonz_cap_to_def pred_tcb_at_def obj_at_def)

lemma send_fault_ipc_not_queued_timeout:
  "\<lbrace>not_queued t and scheduler_act_not t and
    (\<lambda>s. \<forall>xa xb. kheap s (cap_ep_ptr cap) = Some (Endpoint (RecvEP (xa # xb))) \<longrightarrow> xa \<noteq> t)\<rbrace>
      send_fault_ipc tptr cap (Timeout badge) canDonate \<lbrace>\<lambda>rv. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wpsimp wp: send_ipc_not_queued_for_timeout hoare_vcg_conj_lift)
                apply (wpsimp simp: thread_set_def set_object_def)+
  done
(*
lemma send_ipc_valid_sched_for_timeout:
  "\<lbrace>valid_sched and scheduler_act_not tptr and not_queued tptr
(* and
    (\<lambda>s. \<forall>xa xb. kheap s (cap_ep_ptr cap) = Some (Endpoint (RecvEP (xa # xb))) \<longrightarrow> xa \<noteq> t)
*)\<rbrace>
      send_ipc True False (cap_ep_badge cap) True
                 canDonate tptr (cap_ep_ptr cap) \<lbrace>\<lambda>rv. valid_sched \<rbrace>"
  apply (clarsimp simp: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp)
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
  apply (wpsimp wp: hoare_drop_imp get_simple_ko_wp
set_thread_state_not_runnable_valid_sched
 split_del: if_split )
apply (wpsimp wp: sts_st_tcb_at')
apply (clarsimp split del: if_split)


  by (clarsimp simp: ex_nonz_cap_to_def pred_tcb_at_def obj_at_def)

lemma send_fault_ipc_not_queued_timeout:
  "\<lbrace>valid_sched and scheduler_act_not t and
    (\<lambda>s. \<forall>xa xb. kheap s (cap_ep_ptr cap) = Some (Endpoint (RecvEP (xa # xb))) \<longrightarrow> xa \<noteq> t)\<rbrace>
      send_fault_ipc tptr cap (Timeout badge) canDonate \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wpsimp wp: send_ipc_not_queued_for_timeout hoare_vcg_conj_lift)
                apply (wpsimp simp: thread_set_def set_object_def)+
  done
*)

lemma handle_timeout_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t
(*and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)
   and*) \<rbrace>
     handle_timeout tptr (Timeout badge) \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: handle_timeout_def assert_def)
  apply (wpsimp simp:  wp: send_fault_ipc_not_queued_timeout)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (case_tac "tcb_timeout_handler y"; clarsimp)
(*  apply (auto simp: tcb_cnode_map_def caps_of_state_tcb_index_trans)
  apply (drule invs_iflive)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  apply (drule (1) if_live_then_nonz_capD2)
  apply (fastforce simp: live_def split: thread_state.splits)*)
  sorry (* handle_timeout *)
(*
crunches handle_timeout
for valid_sched[wp]: valid_sched
and not_queued[wp]: "not_queued t"
  (wp: maybeM_inv hoare_drop_imps hoare_vcg_if_lift2 valid_sched_lift)
*)
lemma do_reply_transfer_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_objs and ct_active and cte_wp_at ((=) (ReplyCap t')) slot
       and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (case_tac recv_opt; clarsimp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac state)
  apply (case_tac state; clarsimp)
        defer 6
        apply (wpsimp+)[7]
apply (wpsimp wp: )

  apply (wp set_thread_state_not_runnable_valid_sched sts_st_tcb_at'
            do_ipc_transfer_non_null_cte_wp_at2
            thread_set_not_state_valid_sched thread_set_no_change_tcb_state
            possible_switch_to_valid_sched'
         | wpc | clarsimp split del: if_split)+
(*        apply (wp set_thread_state_runnable_valid_ready_qs
                  set_thread_state_runnable_valid_sched_action
                  set_thread_state_valid_blocked_except sts_st_tcb_at')[1]
       apply (rule_tac Q="\<lambda>_. valid_sched and not_cur_thread receiver
                               and (\<lambda>s. receiver \<noteq> idle_thread s)"
              in hoare_strengthen_post)
        apply wp
       apply (simp add: valid_sched_def)
      apply (wp possible_switch_to_valid_sched')+
           apply simp
           apply (rule conjI)
            apply clarsimp
            apply (rule_tac P="valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) receiver
                               and ct_active and (\<lambda>s. receiver \<noteq> idle_thread s)" in hoare_weaken_pre)
             apply (wp set_thread_state_runnable_valid_ready_qs
                       set_thread_state_runnable_valid_sched_action
                       set_thread_state_valid_blocked_except sts_st_tcb_at')[1]
            apply (fastforce simp: valid_sched_def ct_in_state_def st_tcb_at_def not_cur_thread_def
                                  obj_at_def)
           apply clarsimp
           apply (wp set_thread_state_not_runnable_valid_sched)
           apply simp
          apply (wp thread_set_not_state_valid_sched thread_set_no_change_tcb_state
                    cap_delete_one_reply_st_tcb_at thread_set_ct_active_wp | simp add: ct_in_state_def | wps)+
    apply (wp hoare_drop_imps hoare_vcg_all_lift)[1]
   apply (simp add: get_thread_state_def thread_get_def | wp)+
  apply (clarsimp simp: ct_in_state_def cte_wp_at_caps_of_state not_cur_thread_def)
  apply (fastforce simp: st_tcb_def2)
  done*)
sorry (* do_reply_transfer *)

end


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

crunches update_sk_obj_ref
for valid_ready_qs[wp]: valid_ready_qs
and valid_release_q[wp]: valid_release_q
and valid_sched_action[wp]: valid_sched_action
  (simp: crunch_simps sc_tcb_sc_at_def obj_at_def wp: crunch_wps set_object_wp get_simple_ko_wp)

crunches set_thread_state,update_sk_obj_ref,unbind_reply_in_ts
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
                 ssc_bound_tcb_at_cases
                 Arch.test_reschedule_bound_sc_tcb_at
                 Arch.tcb_release_remove_bound_sc_tcb_at
                 Arch.tcb_sched_action_bound_sc_tcb_at) (* why are these in Arch? *)

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
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_release_q_def)
  apply (drule_tac x=t in bspec, simp, clarsimp simp: etcb_defs split: option.splits)
  by (fastforce simp: active_sc_tcb_at_defs refill_prop_defs st_tcb_at_kh_def)

lemma set_sc_replies_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. valid_sched_action::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_sched_action_def is_activatable_def weak_valid_sched_action_def
                        switch_in_cur_domain_def in_cur_domain_def)
  apply (intro conjI impI; clarsimp simp: active_sc_tcb_at_defs st_tcb_at_kh_def split del: if_split)
  by (fastforce simp: etcb_defs)+

lemma reply_push_valid_ready_qs[wp]:
  "\<lbrace>valid_ready_qs and not_queued caller and not_queued callee and scheduler_act_not callee\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_ready_qs::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def unbind_reply_in_ts_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
                 get_simple_ko_wp set_thread_state_not_queued_valid_ready_qs
             split_del: if_split cong: conj_cong)

lemma reply_push_valid_release_q[wp]:
  "\<lbrace>valid_release_q and not_in_release_q caller and not_in_release_q callee and scheduler_act_not callee\<rbrace>
     reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_push_def unbind_reply_in_ts_def)
  by (wpsimp wp: hoare_drop_imp get_sched_context_wp hoare_vcg_if_lift2 hoare_vcg_all_lift
                 get_simple_ko_wp sched_context_donate_valid_release_q
                 set_thread_state_not_queued_valid_release_q
             split_del: if_split cong: conj_cong)


crunches reply_push
for ct_not_in_q[wp]: "ct_not_in_q"
and cur_thread[wp]: "\<lambda>s::det_ext state. P (cur_thread s)"
and not_cur_thread[wp]: "not_cur_thread t"
  (wp: crunch_wps hoare_vcg_if_lift ignore: set_thread_state test_reschedule)

lemma reply_push_valid_sched_helper:
  "\<lbrace> st_tcb_at ((=) Inactive) callee and valid_sched
     and bound_sc_tcb_at ((=) None) callee \<rbrace>
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
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched
                     hoare_drop_imp unbind_reply_in_ts_trivial_inv)+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (intro conjI)
   apply (wpsimp wp: reply_push_valid_sched_helper)
        apply (wpsimp wp: sts_st_tcb_at_other)
        apply (wpsimp wp: reply_push_valid_sched_helper
                          set_thread_state_not_queued_valid_sched
                          set_thread_state_bound_sc_tcb_at)
       apply (wpsimp wp: unbind_reply_in_ts_inv hoare_drop_imp)+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (wpsimp wp: set_thread_state_not_queued_valid_sched
      unbind_reply_in_ts_trivial_inv hoare_drop_imp)+
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
  "\<lbrace>is_refill_ready xa and is_refill_sufficient xa 0 \<rbrace>
     set_tcb_obj_ref tcb_sched_context_update x1 (Some xa)
   \<lbrace>\<lambda>r s. budget_ready x1 s \<and> budget_sufficient x1 s\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
  using get_tcb_SomeD apply fastforce
  done

lemma sc_tcb_update_budget_conditions:
  "\<lbrace>is_refill_ready xa and is_refill_sufficient xa 0 \<rbrace>
     set_sc_obj_ref sc_tcb_update xa (Some x1)
   \<lbrace>\<lambda>xaa s. is_refill_ready xa s \<and> is_refill_sufficient xa 0 s\<rbrace>"
  unfolding set_sc_obj_ref_def
  apply (wpsimp wp: set_object_wp get_object_wp simp: update_sched_context_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def is_refill_sufficient_def)
  done

crunches reschedule_required
  for budget_conditions_r[wp]: "is_refill_ready xa"
  and budget_conditions_s[wp]: "is_refill_sufficient xa k"
  (simp: crunch_simps wp: crunch_wps)

crunches tcb_release_remove
  for budget_conditions_r[wp]: "is_refill_ready xa"
  and budget_conditions_s[wp]: "is_refill_sufficient xa k"
  (simp: is_refill_ready_def is_refill_sufficient_def wp: crunch_wps)

lemma sched_context_donate_weak_budget_conditions:
  "\<lbrace>\<lambda>s. is_refill_ready xa s \<and> is_refill_sufficient xa 0 s\<rbrace>
     sched_context_donate xa x1
   \<lbrace>\<lambda>r s. budget_ready x1 s \<and> budget_sufficient x1 s\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: set_object_wp get_object_wp tcb_sched_context_update_weak_budget_conditions sc_tcb_update_budget_conditions)
  apply (wpsimp wp: set_object_wp get_object_wp simp: test_reschedule_def get_sc_obj_ref_def)+
  done

lemma unbind_reply_in_ts_Receive:
  "\<lbrace>st_tcb_at (\<lambda>st. \<exists>r. st = (BlockedOnReceive ep r)) t\<rbrace>
     unbind_reply_in_ts t \<lbrace>\<lambda>rv. st_tcb_at ((=) (BlockedOnReceive ep None)) t\<rbrace>"
  apply (simp add: unbind_reply_in_ts_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule_tac S="\<exists>r. st = BlockedOnReceive ep r" in hoare_gen_asm'',
         clarsimp simp: pred_tcb_at_def obj_at_def)
  by (case_tac st; simp; wpsimp wp: sts_st_tcb_at')

lemma reply_push_st_tcb_at_Receive:
  "\<lbrace>st_tcb_at ((=) (BlockedOnReceive ep r)) callee and K (callee \<noteq> caller)\<rbrace>
     reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. st_tcb_at ((=) (BlockedOnReceive ep None)) callee\<rbrace>"
  unfolding reply_push_def update_sk_obj_ref_def set_sc_obj_ref_def comp_def
  apply (wpsimp wp: get_simple_ko_wp get_tcb_obj_ref_wp hoare_vcg_if_lift hoare_vcg_all_lift
                    sts_st_tcb_at_cases unbind_reply_in_ts_Receive
       | wp_once hoare_drop_imp)+
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

context DetSchedSchedule_AI begin

lemma send_ipc_valid_sched_helper0:
  "\<lbrace>valid_sched
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
               (active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s))
    and not_cur_thread dest and (\<lambda>s. dest \<noteq> idle_thread s)\<rbrace>
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
   apply (wpsimp wp: possible_switch_to_valid_sched' set_thread_state_break_valid_sched
                     hoare_vcg_imp_lift sts_st_tcb_at')
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac Q="bound_sc_tcb_at ((=) (Some a)) dest and valid_sched and
           (\<lambda>s. active_sc_tcb_at dest s \<and>
                budget_ready dest s \<and> budget_sufficient dest s) and
            not_cur_thread dest and (\<lambda>s. dest \<noteq> idle_thread s)" in hoare_weaken_pre)
   apply (wpsimp wp: possible_switch_to_valid_sched' set_thread_state_break_valid_sched
                     hoare_drop_imp sts_st_tcb_at')
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma send_ipc_valid_sched_helper_no_reply:
  "\<lbrace>st_tcb_at ((=) (BlockedOnReceive ep None)) dest and valid_sched
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
            (active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s))
    and not_cur_thread dest and (\<lambda>s. dest \<noteq> idle_thread s)
    and active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr\<rbrace>
   do
     sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then return ()
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
   apply (wpsimp wp: send_ipc_valid_sched_helper0)
  (* false for the first if *)
  apply (case_tac sc_opt; clarsimp simp: bind_assoc split del: if_split)
   apply (rule_tac Q="obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_fault tcb = None) tptr and
            (bound_sc_tcb_at ((=) None) dest and
            (st_tcb_at ((=) (BlockedOnReceive ep None)) dest and valid_sched and
             not_cur_thread dest and (\<lambda>s. dest \<noteq> idle_thread s) and
             active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr))"
          in hoare_weaken_pre)
    apply (clarsimp simp: bind_assoc)
    apply (rule conjI; clarsimp)
     (* donation happens *)
     apply (rule hoare_seq_ext[OF _ gsc_sp])
     apply (wpsimp wp: hoare_drop_imp set_thread_state_break_valid_sched sts_st_tcb_at'
                       possible_switch_to_valid_sched' sched_context_donate_valid_sched
                       sched_context_donate_active_sc_tcb_at_donate
                       sched_context_donate_weak_budget_conditions
                       cong: conj_cong)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
     apply (rename_tac tcb' scp, case_tac "tcb_state tcb'" ; clarsimp)
    (* no donation *)
  by (wpsimp wp: send_ipc_valid_sched_helper0 | simp)+

lemma update_sk_obj_ref_is_refill_ready[wp]:
  "update_sk_obj_ref C f ref new \<lbrace>is_refill_ready scp::det_state \<Rightarrow> _\<rbrace>"
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
  "set_sc_obj_ref sc_replies_update ref list \<lbrace>is_refill_ready scp::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: is_refill_ready_def obj_at_def)

lemma set_sc_replies_is_refill_sufficient[wp]:
  "set_sc_obj_ref sc_replies_update ref list \<lbrace>is_refill_sufficient scp 0::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: is_refill_sufficient_def obj_at_def)

lemma reply_push_active_sc_tcb_at_helper:
  "\<lbrace> test_sc_refill_max sc_ptr and is_refill_ready sc_ptr and is_refill_sufficient sc_ptr 0
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
  "\<lbrace> active_sc_tcb_at caller and budget_ready caller and budget_sufficient caller
     and (\<lambda>s. bound_sc_tcb_at ((=) None) callee s \<or>
         active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s)\<rbrace>
     reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv s::det_state. (bound_sc_tcb_at ((=) None) callee s \<or>
         active_sc_tcb_at callee s \<and> budget_ready callee s \<and> budget_sufficient callee s)\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_thread_state_not_queued_valid_sched unbind_reply_in_ts_trivial_inv
                     hoare_drop_imp hoare_vcg_disj_lift set_thread_state_bound_sc_tcb_at)+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (intro conjI impI)
   apply (rule_tac Q="\<lambda>_ s. ((\<not>can_donate \<longrightarrow> bound_sc_tcb_at ((=) None) callee s) \<and>
                             (can_donate \<longrightarrow> active_sc_tcb_at callee s \<and>
                                 budget_ready callee s \<and> budget_sufficient callee s))"
            in hoare_strengthen_post)
    apply (wpsimp wp: reply_push_active_sc_tcb_at_helper)
     apply (wpsimp wp: reply_push_active_sc_tcb_at_helper sts_st_tcb_at_other
                       set_thread_state_bound_sc_tcb_at hoare_drop_imp)+
    apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
   apply clarsimp
  by (wpsimp wp: sts_st_tcb_at_other hoare_vcg_disj_lift
                     set_thread_state_bound_sc_tcb_at hoare_drop_imp)

lemma send_ipc_valid_sched_helper_some_reply:
  "\<lbrace>(\<lambda>s. \<exists>rptr. st_tcb_at ((=) Inactive) dest s \<and> reply = Some rptr) and valid_sched
       and scheduler_act_not tptr and not_queued tptr and not_in_release_q tptr
       and st_tcb_at active tptr
       and active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr
       and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
                 active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s)
       and not_cur_thread dest and (\<lambda>s. dest \<noteq> idle_thread s)\<rbrace>
  do sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then when (cg \<and> (\<exists>y. reply = Some y))
                  (reply_push tptr dest (the reply) can_donate)
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
              not_cur_thread dest and
              (\<lambda>s. dest \<noteq> idle_thread s) and
              active_sc_tcb_at tptr and
              budget_ready tptr and
              budget_sufficient tptr))" in hoare_weaken_pre)
    apply (case_tac "call \<or> (\<exists>y. fault = Some y)"; simp split del: if_split)
    (* true for the first if *)
     apply (clarsimp simp: bind_assoc)
     apply (rule conjI; clarsimp)
    (* reply_push *)
      apply (wpsimp wp: send_ipc_valid_sched_helper0 reply_push_st_tcb_at_Inactive wp_del: reply_push_st_tcb_at)
       apply (wpsimp wp: set_thread_state_break_valid_sched reply_push_valid_sched
                         possible_switch_to_valid_sched' sts_st_tcb_at'
                         hoare_drop_imp reply_push_active_sc_tcb_at)
      apply (clarsimp simp: pred_tcb_at_def active_sc_tcb_at_def obj_at_def)
    (* no reply push *)
     apply (wpsimp wp: send_ipc_valid_sched_helper0)
    (* false for the first if *)
    apply (clarsimp simp: bind_assoc)
    apply (rule conjI; clarsimp)
    (* donation happens *)
     apply (rule hoare_seq_ext[OF _ gsc_sp])
     apply (wpsimp wp: hoare_drop_imp set_thread_state_break_valid_sched sts_st_tcb_at'
                       possible_switch_to_valid_sched' sched_context_donate_valid_sched
                       sched_context_donate_active_sc_tcb_at_donate
                       sched_context_donate_weak_budget_conditions
                 cong: conj_cong)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def active_sc_tcb_at_def)
   (* dest has no sc (no donation) *)
    apply (wpsimp wp: send_ipc_valid_sched_helper0)
   apply clarsimp
  apply (wpsimp wp: send_ipc_valid_sched_helper0 reply_push_st_tcb_at_Inactive wp_del: reply_push_st_tcb_at)
  by (wpsimp wp: set_thread_state_break_valid_sched reply_push_valid_sched
                 possible_switch_to_valid_sched' sts_st_tcb_at' hoare_drop_imp
                 reply_push_active_sc_tcb_at
           cong: conj_cong)+

crunches do_ipc_transfer
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state.  (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state.  (budget_sufficient t s)"
and not_in_release_q[wp]: "\<lambda>s:: det_ext state.  (not_in_release_q t s)"
  (wp: crunch_wps maybeM_wp transfer_caps_loop_pres simp: crunch_simps)

lemma do_ipc_transfer_bound_sc':
  "do_ipc_transfer sender ep badge grant receiver \<lbrace>bound_sc_tcb_at P t::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def
               wp: do_normal_transfer_bound_sc do_fault_transfer_bound_sc)

lemma send_ipc_valid_sched_helper:
  "\<lbrace>valid_sched and scheduler_act_not tptr and not_queued tptr
    and not_in_release_q tptr and st_tcb_at active tptr
    and active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr
    and (\<lambda>s. bound_sc_tcb_at ((=) None) dest s \<or>
           active_sc_tcb_at dest s \<and> budget_ready dest s \<and> budget_sufficient dest s)
    and (\<lambda>s. dest \<noteq> idle_thread s) and not_cur_thread dest
    and (\<lambda>s. st_tcb_at (\<lambda>st. \<forall>epptr. \<forall>rp. st = BlockedOnReceive epptr (Some rp)
                            \<longrightarrow> reply_tcb_reply_at (\<lambda>a. a = Some dest) rp s) dest s)\<rbrace>
   do recv_state <- get_thread_state dest;
      reply <- case recv_state of BlockedOnReceive x reply \<Rightarrow>
                         return reply
               | _ \<Rightarrow> fail;
      y \<leftarrow> do_ipc_transfer tptr (Some epptr) ba cg dest;
      y \<leftarrow> maybeM reply_unlink_tcb reply;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then when (cg \<and> (\<exists>y. reply = Some y))
                  (reply_push tptr dest (the reply) can_donate)
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
  apply (case_tac recv_state; simp)
  apply (rename_tac r)
  apply (case_tac r, simp)
   apply (wpsimp wp: send_ipc_valid_sched_helper_no_reply
                     do_ipc_transfer_bound_sc' hoare_vcg_disj_lift)
  apply (wpsimp wp: send_ipc_valid_sched_helper_some_reply wp_del: maybeM_wp)
    apply (wpsimp wp: reply_unlink_tcb_valid_sched hoare_drop_imp
                      reply_unlink_runnable[simplified runnable_eq_active]
                      do_ipc_transfer_bound_sc' hoare_vcg_disj_lift
                      reply_unlink_tcb_bound_sc_tcb_at)
   apply (wpsimp wp: do_ipc_transfer_bound_sc' hoare_vcg_disj_lift)
  apply (clarsimp simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def)
  apply (drule_tac x=x41 and y=a in spec2)
  apply clarsimp
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
    and active_sc_tcb_at thread and budget_ready thread and budget_sufficient thread\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases block, simp_all)[1]
     apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
    apply wpsimp
   apply (cases block, simp_all)[1]
    apply (wpsimp wp: set_thread_state_not_queued_valid_sched)
   apply wpsimp
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: send_ipc_valid_sched_helper set_simple_ko_pred_tcb_at hoare_vcg_disj_lift)
   apply (wpsimp simp: set_simple_ko_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: obj_at_def valid_ep_q_def)
  apply (drule_tac x=epptr in spec)
  apply (clarsimp simp: ep_blocked_def pred_tcb_at_def obj_at_def split: option.splits)
  apply (clarsimp simp: obj_at_def partial_inv_def)
  apply (rule conjI; clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def not_cur_thread_def)
  apply (rule conjI; clarsimp)
  apply (frule invs_valid_objs)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb)
  apply (frule invs_sym_refs)
  apply (drule_tac tp=dest in sym_ref_tcb_reply_Receive)
    apply simp
   apply simp
  apply (clarsimp simp: valid_obj_def valid_ep_def obj_at_def is_tcb reply_tcb_reply_at_def)
  done

end

lemma thread_set_tcb_fault_set_invs:
  "valid_fault f \<Longrightarrow> \<lbrace>invs\<rbrace>
     thread_set (tcb_fault_update (\<lambda>_. Some f)) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule thread_set_invs_trivial)
      apply (clarsimp simp: ran_tcb_cap_cases)+
  done

lemma thread_set_valid_ep_q:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
    \<lbrace>valid_ep_q\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_ep_q\<rbrace>"
  apply (wpsimp simp: thread_set_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_ep_q_def dest!: get_tcb_SomeD split: option.splits)
  apply (drule_tac x=p in spec; clarsimp)
  apply (rename_tac ko; case_tac ko; clarsimp)
  apply (drule_tac x=t in bspec, simp, clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
   apply (rename_tac ep; case_tac ep; clarsimp)
  apply (erule disjE)
   apply (clarsimp simp: bound_sc_tcb_at_kh_if_split pred_tcb_at_def obj_at_def)
  apply (rule disjI2)
  apply (clarsimp simp: active_sc_tcb_at_defs st_tcb_at_kh_def refill_prop_defs)
  by (intro conjI impI; (rule_tac x=scpb in exI; fastforce))

context DetSchedSchedule_AI begin
lemma send_fault_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched and st_tcb_at active tptr and scheduler_act_not tptr and valid_ep_q
     and not_queued tptr and (ct_active or ct_idle) and invs and (\<lambda>_. valid_fault fault)
     and not_in_release_q tptr
     and active_sc_tcb_at tptr and budget_ready tptr and budget_sufficient tptr\<rbrace>
    send_fault_ipc tptr handler_cap fault can_donate
     \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_fault_ipc_def Let_def)
  apply (case_tac handler_cap; wpsimp)
                by (wp send_ipc_valid_sched thread_set_not_state_valid_sched
                          thread_set_no_change_tcb_state
                          hoare_gen_asm'[OF thread_set_tcb_fault_set_invs]
                          hoare_drop_imps hoare_vcg_all_lift_R
                          ct_in_state_thread_state_lift
                          thread_set_no_change_tcb_state
                          thread_set_valid_ep_q
                          thread_set_active_sc_tcb_at
                          budget_ready_thread_set_no_change
                          budget_sufficient_thread_set_no_change
                          hoare_vcg_disj_lift
                          | wpc | simp | wps)+

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
  apply (wp | simp add:   set_object_def)+
  apply (clarsimp simp: valid_release_q_def st_tcb_at_kh_if_split not_in_release_q_def
                 dest!: get_tcb_SomeD)
  apply (drule_tac x=t in bspec, simp)
  apply (clarsimp simp: active_sc_tcb_at_defs, intro conjI impI, fastforce+)
  apply (rename_tac scp, rule_tac x=scp in exI, fastforce)+
  done

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
            set_thread_state_not_runnable_valid_blocked handle_no_fault_valid_release_q
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
lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and not_queued thread and not_in_release_q thread
      and scheduler_act_not thread and invs and (\<lambda>_. valid_fault ex)
      and valid_ep_q and (ct_active or ct_idle)
      and active_sc_tcb_at thread and budget_ready thread and budget_sufficient thread\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_fault_def unless_def
  apply (wpsimp wp: handle_no_fault_valid_sched send_fault_ipc_valid_sched hoare_vcg_if_lift2
                    hoare_drop_imps hoare_vcg_conj_lift)
sorry (* ? handle_fault *)

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

lemma reply_remove_tcb_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at t \<rbrace>
     reply_remove_tcb tptr
   \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply wpsimp
  done

crunches cancel_ipc
  for active_sc_tcb_at: "active_sc_tcb_at t::det_state \<Rightarrow> _"
  (wp: hoare_drop_imp crunch_wps)

lemma not_not_in_eq_in[iff]: "\<not> not_in_release_q t s \<longleftrightarrow> in_release_queue t s"
  by (clarsimp simp: in_release_queue_def not_in_release_q_def)

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
  "\<lbrace>test_sc_refill_max xa::det_state \<Rightarrow> _\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update x1 (Some xa)
   \<lbrace>\<lambda>r. active_sc_tcb_at x1\<rbrace>"
  unfolding set_tcb_obj_ref_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def
                        test_sc_refill_max_def)
  using get_tcb_SomeD by fastforce

crunch active_sc_tcb_at[wp]: postpone "\<lambda>s. active_sc_tcb_at x s"
  (simp: crunch_simps wp: crunch_wps)

lemma sched_context_resume_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at x1\<rbrace>
     sched_context_resume sc_ptr
   \<lbrace>\<lambda>r. active_sc_tcb_at x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: thread_get_wp is_schedulable_wp)
  apply (fastforce simp: obj_at_def is_schedulable_opt_def
                  split: option.splits
                  dest!: get_tcb_SomeD)
  done

lemma refill_unblock_check_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at x1\<rbrace>
     refill_unblock_check sc_ptr
   \<lbrace>\<lambda>r. active_sc_tcb_at x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (fastforce simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def
                  split: option.splits
                  dest!: get_tcb_SomeD)
  done

lemma maybe_donate_sc_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at x1 and active_sc_ntfn_at ntfnptr\<rbrace>
     maybe_donate_sc x1 ntfnptr
   \<lbrace>\<lambda>r. active_sc_tcb_at x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def sched_context_donate_def active_sc_ntfn_at_def
  apply (wpsimp wp: tcb_sched_context_update_active_sc_tcb_at get_sc_obj_ref_wp
                 get_sk_obj_ref_wp get_tcb_obj_ref_wp)
  by (simp add: bound_sc_ntfn_at_kh_def obj_at_def)

lemma maybe_donate_sc_budget_conditions:
  "\<lbrace>(\<lambda>s. (budget_ready x1 s \<and> budget_sufficient x1 s)) and budgeted_sc_ntfn_at ntfnptr\<rbrace>
     maybe_donate_sc x1 ntfnptr
   \<lbrace>\<lambda>r s. (budget_ready x1 s \<and> budget_sufficient x1 s)\<rbrace>"
  unfolding maybe_donate_sc_def budgeted_sc_ntfn_at_def
  apply (clarsimp)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; clarsimp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp wp: set_object_wp get_object_wp sc_tcb_update_budget_conditions get_simple_ko_wp
                     sched_context_donate_weak_budget_conditions refill_unblock_check_budget_ready
                     refill_unblock_check_budget_sufficient
            simp: set_tcb_obj_ref_def set_sc_obj_ref_def get_sc_obj_ref_def get_sk_obj_ref_def
                  get_tcb_obj_ref_def thread_get_def)
   apply (subgoal_tac "obj=ntfn"; (clarsimp simp: obj_at_def))
  apply wpsimp
  done

lemma as_user_has_budget[wp]:
  "\<lbrace>has_budget x1\<rbrace> as_user ptr s \<lbrace>\<lambda>_. has_budget x1\<rbrace>"
  by (wpsimp wp: as_user_budget_ready as_user_budget_sufficient
                 as_user_active_sc_tcb_at as_user_pred_tcb_at hoare_vcg_disj_lift
           simp: has_budget_def)

lemma tcb_sched_context_update_has_budget:
  "\<lbrace>test_sc_refill_max xa and is_refill_sufficient xa 0 and is_refill_ready xa\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update x1 (Some xa)
   \<lbrace>\<lambda>r. has_budget x1\<rbrace>"
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
  "\<lbrace>\<lambda>s. test_sc_refill_max xa s \<and> is_refill_sufficient xa 0 s \<and> is_refill_ready xa s \<and>
        sc_tcb_sc_at (\<lambda>t. t = None) xa s\<rbrace>
   sched_context_donate xa x1
   \<lbrace>\<lambda>r. has_budget x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_donate_def
  apply (wpsimp wp: tcb_sched_context_update_has_budget set_sc_refills_inv_is_refill_ready
                    set_sc_refills_inv_is_refill_sufficient test_reschedule_case
              simp: get_sc_obj_ref_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_resume_has_budget:
  "\<lbrace>has_budget x1 and bound_sc_tcb_at ((=) (Some xa)) x1 \<rbrace>
   sched_context_resume xa
   \<lbrace>\<lambda>r. has_budget x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding sched_context_resume_def
  apply (wpsimp wp: )
  apply (rule hoare_pre_cont)
  apply (wpsimp simp: thread_get_def wp: is_schedulable_wp)+
  apply (fastforce simp: is_refill_ready_def is_refill_sufficient_def obj_at_def bound_sc_tcb_at_def
                        has_budget_def)
  done


lemma refill_unblock_check_has_budget:
  "\<lbrace>has_budget x1 and bound_sc_tcb_at ((=) (Some xa)) x1\<rbrace>
   refill_unblock_check xa
   \<lbrace>\<lambda>r. has_budget x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding refill_unblock_check_def
  apply (wpsimp wp: set_refills_wp get_refills_wp is_round_robin_wp)
  apply (clarsimp simp: has_budget_equiv)
  apply (intro conjI impI)
     apply (clarsimp simp: obj_at_def is_tcb)
    apply (fastforce simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                          active_sc_tcb_at_def test_sc_refill_max_def)
   apply (fastforce simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                         active_sc_tcb_at_def is_refill_sufficient_def)
  apply (clarsimp simp: pred_tcb_at_eq_commute bound_sc_tcb_at_def obj_at_def is_tcb
                        active_sc_tcb_at_def is_refill_ready_def)
  apply (safe; clarsimp)
  apply (clarsimp simp: r_time_hd_refills_merge_prefix)
  apply (rule cur_time_assumption)
  done

lemma sched_context_donate_bound_sc_tcb_at:
  "\<lbrace>\<top>\<rbrace> sched_context_donate xa x1 \<lbrace>\<lambda>rv. bound_sc_tcb_at ((=) (Some xa)) x1\<rbrace>"
  unfolding sched_context_donate_def
  by (wpsimp wp: ssc_bound_tcb_at')

lemma maybe_donate_sc_has_budget:
  "\<lbrace>has_budget x1 and active_sc_ntfn_at ntfnptr and budgeted_sc_ntfn_at ntfnptr\<rbrace>
     maybe_donate_sc x1 ntfnptr
   \<lbrace>\<lambda>r. has_budget x1 :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  apply (wpsimp wp: sched_context_donate_has_budget sched_context_resume_has_budget)
  apply (wpsimp wp: refill_unblock_check_has_budget)
  apply (clarsimp simp:)
  apply (wpsimp wp: sched_context_donate_has_budget sched_context_donate_bound_sc_tcb_at)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift get_simple_ko_wp
              simp: get_sk_obj_ref_def get_sc_obj_ref_def get_tcb_obj_ref_def thread_get_def)+
  apply (clarsimp simp: budgeted_sc_ntfn_at_def active_sc_ntfn_at'_def bound_sc_ntfn_at_kh_def
                        obj_at_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma valid_sched_release_queue_runnable:
  "valid_sched s \<Longrightarrow> t \<in> set (release_queue s) \<Longrightarrow> st_tcb_at runnable t s"
  by (clarsimp simp: valid_sched_def valid_release_q_def)

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

lemma as_user_active_sc_ntfn_at'[wp]:
  "\<lbrace>active_sc_ntfn_at' ntfnptr\<rbrace>
   as_user tcbptr f
   \<lbrace>\<lambda>rv. active_sc_ntfn_at' ntfnptr\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  apply (clarsimp simp: active_sc_ntfn_at'_def bound_sc_ntfn_at_kh_def obj_at_kh_def
                        test_sc_refill_max_kh_def
                  dest!: get_tcb_SomeD split: option.splits)
  apply (intro conjI impI, fastforce)
  apply (rule_tac x=scp in exI, fastforce)
  done

lemma as_user_budgeted_sc_ntfn_at[wp]:
  "\<lbrace>budgeted_sc_ntfn_at ntfnptr\<rbrace>
   as_user tcbptr f
   \<lbrace>\<lambda>rv. budgeted_sc_ntfn_at ntfnptr\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def)
  apply (clarsimp simp: budgeted_sc_ntfn_at_def obj_at_def is_refill_sufficient_def
                        is_refill_ready_def sufficient_refills_def
                  dest!: get_tcb_SomeD split: option.splits)
  apply (intro conjI impI, fastforce)
  apply (rule_tac x=xb in exI, fastforce)
  done

lemma maybe_donate_sc_ct_not_in_q2:
  "\<lbrace> ct_not_in_q and has_budget tcb_ptr\<rbrace>
     maybe_donate_sc tcb_ptr ntfnptr
   \<lbrace> \<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  unfolding maybe_donate_sc_def
  by (wpsimp wp: get_sc_obj_ref_wp get_sk_obj_ref_wp get_tcb_obj_ref_wp)

lemma set_thread_state_active_sc_ntfn_at'[wp]:
  "\<lbrace>active_sc_ntfn_at' ntfnptr\<rbrace>
     set_thread_state x1 st
   \<lbrace>\<lambda>rv. active_sc_ntfn_at' ntfnptr\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp simp: set_object_def)
  apply (clarsimp simp: dest!: get_tcb_SomeD)
  apply (clarsimp simp: active_sc_ntfn_at_kh_def bound_sc_ntfn_at_kh_def test_sc_refill_max_kh_def
                        obj_at_kh_def)
  apply (intro conjI impI, fastforce)
  apply (rule_tac x=scp in exI, fastforce)
  done

crunch budgeted_sc_ntfn_at[wp]: set_scheduler_action "budgeted_sc_ntfn_at ntfnptr"
  (simp: budgeted_sc_ntfn_at_def)

lemma set_thread_state_budgeted_sc_ntfn_at[wp]:
  "set_thread_state a b \<lbrace>budgeted_sc_ntfn_at ntfnptr::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: budgeted_sc_ntfn_at_def obj_at_def is_refill_ready_def
                        is_refill_sufficient_def
                 split: option.splits)
  apply (subgoal_tac "ntfnptr \<noteq> a", simp)
  apply (rule_tac x=x in exI; fastforce dest!: get_tcb_SomeD)
  apply (fastforce dest!: get_tcb_SomeD)
  done


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

crunch budgeted_sc_ntfn_at[wp]: set_simple_ko "budgeted_sc_ntfn_at ntfnptr"
  (wp: set_object_wp crunch_wps)

lemma valid_sched_not_runnable_not_in_release_q:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (fastforce simp: valid_sched_def valid_release_q_def pred_tcb_at_def
                      not_queued_def not_in_release_q_def obj_at_def)

lemma valid_sched_not_runnable_not_queued:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s"
  by (fastforce simp: valid_sched_def valid_ready_qs_def  pred_tcb_at_def
                      not_queued_def  obj_at_def)

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

lemma send_signal_WaitingNtfn_helper:
  "ntfn_obj ntfn = WaitingNtfn wnlist \<Longrightarrow>
   \<lbrace>ko_at (Notification ntfn) ntfnptr and (valid_sched and invs) and
    st_tcb_at ((=) (BlockedOnNotification ntfnptr)) (hd wnlist) and not_cur_thread (hd wnlist) and
    active_sc_ntfn_at ntfnptr and budgeted_sc_ntfn_at ntfnptr and has_budget (hd wnlist) and
    valid_ntfn_q\<rbrace>
   update_waiting_ntfn ntfnptr wnlist (ntfn_bound_tcb ntfn) (ntfn_sc ntfn) badge
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wpsimp wp: possible_switch_to_valid_sched3)
        apply_trace (wpsimp wp: maybe_donate_sc_valid_ready_qs
                          maybe_donate_sc_valid_release_q
                          maybe_donate_sc_valid_sched_action
                          maybe_donate_sc_ct_not_in_q2
                          maybe_donate_sc_ct_in_cur_domain
                          maybe_donate_sc_active_sc_tcb_at
                          maybe_donate_sc_budget_conditions
                          maybe_donate_sc_valid_blocked_except_set
                          maybe_donate_sc_has_budget
                          hoare_vcg_imp_lift'')
       apply wpsimp
      apply (rule_tac Q="\<lambda>xc s. (valid_sched_except_blocked s \<and> valid_blocked_except_set {x1} s)
                         \<and>
                  not_queued x1 s \<and>
                  not_cur_thread x1 s \<and>
                  st_tcb_at runnable x1 s \<and> scheduler_act_not x1 s \<and> not_in_release_q x1 s \<and>
                  has_budget x1 s \<and> active_sc_ntfn_at' ntfnptr s \<and> budgeted_sc_ntfn_at ntfnptr s"
                      in hoare_strengthen_post[rotated])
       apply (clarsimp)
      apply (rule hoare_vcg_conj_lift)
       apply (rule set_thread_state_break_valid_sched[simplified pred_conj_def])
      apply (wpsimp wp: sts_st_tcb_at')
     apply simp
     apply (wpsimp wp: set_simple_ko_valid_sched set_simple_ko_budgeted_sc_ntfn_at set_simple_ko_wp)
    apply wpsimp+
  apply (intro conjI)
       apply (erule valid_sched_not_runnable_not_queued)
       apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
      apply (erule valid_sched_not_runnable_scheduler_act_not)
      apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
     apply (erule valid_sched_not_runnable_not_in_release_q)
     apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
    apply (subst has_budget_update_ntfn;
           clarsimp simp: obj_at_def ntfn_at_pred_def is_ntfn_def)
   apply (clarsimp simp: active_sc_ntfn_at_kh_def bound_sc_ntfn_at_kh_def obj_at_kh_def
                         test_sc_refill_max_kh_def obj_at_def)
   apply (rule_tac x=scp in exI; fastforce)
  apply (clarsimp simp: budgeted_sc_ntfn_at_def is_refill_ready_def is_refill_sufficient_def obj_at_def)
  apply (rule_tac x=x in exI; fastforce)
  done

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
         apply (wpsimp+)[3]
      apply (wpsimp wp: blocked_cancel_ipc_BOR_valid_sched')
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

lemma blocked_cancel_ipc_BOR_active_sc_tcb_at:
  "\<lbrace>active_sc_tcb_at tcbptr\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r1) tcbptr r2
   \<lbrace>\<lambda>rv. active_sc_tcb_at tcbptr :: det_state \<Rightarrow> _\<rbrace>"
  unfolding blocked_cancel_ipc_def
  by (wpsimp wp: reply_unlink_tcb_active_sc_tcb_at hoare_drop_imps)

crunch active_sc_ntfn_at[wp]: set_scheduler_action "active_sc_ntfn_at ntfnptr"
  (simp: active_sc_ntfn_at_def )

crunch active_sc_ntfn_at[wp]: set_simple_ko "active_sc_ntfn_at ntfnptr"
  (wp: set_object_wp crunch_wps
 simp: active_sc_ntfn_at_kh_def bound_sc_ntfn_at_kh_def
       obj_at_kh_def test_sc_refill_max_def test_sc_refill_max_kh_def)

lemmas active_sc_ntfn_at_defs = active_sc_ntfn_at_kh_def test_sc_refill_max_kh_def
                                bound_sc_ntfn_at_kh_def obj_at_kh_def

lemma blocked_cancel_ipc_BOR_active_sc_ntfn_ata[wp]:
  "set_thread_state a b \<lbrace>active_sc_ntfn_at ntfnptr::det_state \<Rightarrow> _\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: active_sc_ntfn_at_defs test_sc_refill_max_def obj_at_def
                  dest!: get_tcb_SomeD
                  split: option.splits)
  done

lemma blocked_cancel_ipc_BOR_active_sc_ntfn_atb[wp]:
  "\<lbrace>active_sc_ntfn_at ntfnptr and valid_objs\<rbrace>
      reply_unlink_tcb repptr
   \<lbrace>\<lambda>rv. active_sc_ntfn_at ntfnptr::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp simp: get_thread_state_def wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp)
  apply (clarsimp simp: active_sc_ntfn_at_defs test_sc_refill_max_def obj_at_def reply_at_pred_def split: option.splits)
  apply (subgoal_tac "ntfnptr \<noteq> repptr"; (simp add: )?)
  apply (erule (1) pspace_valid_objsE, clarsimp simp: valid_obj_def valid_reply_def tcb_at_def dest!: get_tcb_SomeD)
  apply fastforce+
 done

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

lemma blocked_cancel_ipc_BOR_active_sc_ntfn_at:
  "\<lbrace>st_tcb_at (\<lambda>st. st = BlockedOnReceive ep r) tcbptr and active_sc_ntfn_at ntfnptr and valid_objs\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r) tcbptr r
   \<lbrace>\<lambda>rv. active_sc_ntfn_at ntfnptr::det_state \<Rightarrow> _\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp get_ep_queue_wp get_blocking_object_wp)
  apply (intro impI conjI allI; clarsimp simp: active_sc_ntfn_at_defs test_sc_refill_max_def obj_at_def ep_at_pred_def reply_at_pred_def split: option.splits)
       prefer 4
       apply ((intro conjI allI impI | fastforce | rule_tac x=x in exI)+)[2]
     prefer 3
     apply ((intro conjI allI impI | fastforce | rule_tac x=xa in exI)+)[2]
   apply (rule valid_objs_ep_update; (clarsimp simp: obj_at_def is_ep_def)?)
   apply (subgoal_tac "valid_ep (SendEP q) s")
    apply (rule valid_ep_remove1_SendEP; simp)
  using valid_ep_valid_objs apply fastforce
  apply (rule valid_objs_ep_update; (clarsimp simp: obj_at_def is_ep_def)?)
  apply (subgoal_tac "valid_ep (RecvEP q) s")
   apply (rule valid_ep_remove1_RecvEP; simp)
  using valid_ep_valid_objs apply fastforce
  done

lemma reply_unlink_tcb_budgeted_sc_ntfn_at[wp]:
  "\<lbrace>budgeted_sc_ntfn_at ntfnptr and valid_objs\<rbrace>
      reply_unlink_tcb r
   \<lbrace>\<lambda>rv. budgeted_sc_ntfn_at ntfnptr::det_state \<Rightarrow> _\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp simp: get_thread_state_def wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp)
  apply (clarsimp simp: budgeted_sc_ntfn_at_def test_sc_refill_max_def obj_at_def reply_at_pred_def split: option.splits)
  apply (subgoal_tac "ntfnptr \<noteq> r"; (simp add: )?)
  apply (erule (1) pspace_valid_objsE, clarsimp simp: valid_obj_def valid_reply_def tcb_at_def dest!: get_tcb_SomeD)
  apply (auto simp: is_refill_ready_def obj_at_def is_refill_sufficient_def)
 done

lemma blocked_cancel_ipc_BOR_budgeted_sc_ntfn_at:
  "\<lbrace>budgeted_sc_ntfn_at ntfnptr and valid_objs\<rbrace>
      blocked_cancel_ipc (BlockedOnReceive ep r1) tcbptr r2
   \<lbrace>\<lambda>rv. budgeted_sc_ntfn_at ntfnptr :: det_state \<Rightarrow> _\<rbrace>"
  unfolding blocked_cancel_ipc_def
  apply (wpsimp simp: get_thread_state_def wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp get_ep_queue_wp get_blocking_object_wp)
  apply (intro impI conjI allI; clarsimp simp: budgeted_sc_ntfn_at_def test_sc_refill_max_def obj_at_def ep_at_pred_def reply_at_pred_def is_refill_ready_def is_refill_sufficient_def split: option.splits)
       prefer 4
       apply ((intro conjI allI impI | fastforce | rule_tac x=x in exI)+)[2]
     prefer 3
     apply ((intro conjI allI impI | fastforce | rule_tac x=xa in exI)+)[2]
   apply (rule valid_objs_ep_update; (clarsimp simp: obj_at_def is_ep_def)?)
   apply (subgoal_tac "valid_ep (SendEP q) s")
    apply (rule valid_ep_remove1_SendEP; simp)
  apply (fastforce intro: valid_ep_valid_objs)
  apply (rule valid_objs_ep_update; (clarsimp simp: obj_at_def is_ep_def)?)
  apply (subgoal_tac "valid_ep (RecvEP q) s")
   apply (rule valid_ep_remove1_RecvEP; simp)
  apply (fastforce intro: valid_ep_valid_objs)
  done

crunch weak_budget_conditions[wp]: set_scheduler_action "\<lambda>s. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)"
  (simp: budgeted_sc_ntfn_at_def )

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
   reply_unlink_tcb r
   \<lbrace>\<lambda>rv s::det_state. (not_in_release_q tcbptr s \<longrightarrow> budget_ready tcbptr s \<and> budget_sufficient tcbptr s)\<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wpsimp simp: get_thread_state_def wp: thread_get_wp get_simple_ko_wp set_simple_ko_wp)
  apply (clarsimp simp: budgeted_sc_ntfn_at_def test_sc_refill_max_def obj_at_def reply_at_pred_def
                 split: option.splits)
  apply (erule (1) pspace_valid_objsE,
         clarsimp simp: valid_obj_def valid_reply_def tcb_at_def
                 dest!: get_tcb_SomeD)
  apply (intro conjI allI impI;
         clarsimp simp: pred_tcb_at_def is_refill_ready_def obj_at_def is_refill_sufficient_def
                        in_release_queue_def not_in_release_q_def)
     apply (intro conjI allI impI | fastforce | rule_tac x=scpa in exI)+
 done

(* FIXME: why are we passing around n for is_sched_sc ?! *)
term is_SchedContext

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
        (\<lambda>s. not_queued tcbptr s \<and>
                 scheduler_act_not tcbptr s \<and>
                 not_in_release_q tcbptr s \<and>
                 not_cur_thread tcbptr s \<and>
                 active_sc_ntfn_at' ntfnptr s \<and> has_budget tcbptr s \<and> budgeted_sc_ntfn_at ntfnptr s)\<rbrace>
      cancel_ipc tcbptr
   \<lbrace>\<lambda>rv s::det_state. not_queued tcbptr s \<and>
                 scheduler_act_not tcbptr s \<and>
                 not_in_release_q tcbptr s \<and>
                 not_cur_thread tcbptr s \<and>
                 active_sc_ntfn_at' ntfnptr s \<and> has_budget tcbptr s \<and> budgeted_sc_ntfn_at ntfnptr s\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state; clarsimp)
         prefer 4
         apply (wpsimp wp: blocked_cancel_ipc_not_cur_thread
                           blocked_cancel_ipc_BOR_has_budget
                           blocked_cancel_ipc_BOR_active_sc_ntfn_at
                           blocked_cancel_ipc_BOR_budgeted_sc_ntfn_at)
         apply (intro conjI; clarsimp elim!: st_tcb_at_tcb_at simp: pred_tcb_at_eq_commute)
        apply (rule hoare_weaken_pre,
               rule hoare_pre_cont
               | clarsimp simp: st_tcb_at_def obj_at_def
               | case_tac "tcb_state tcb")+
  done

lemma send_signal_BOR_helper:
  "ntfn_obj ntfn = IdleNtfn
   \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr
   \<Longrightarrow> \<lbrace>st_tcb_at ((=) (BlockedOnReceive x41 x42)) tcbptr and (ko_at (Notification ntfn) ntfnptr and
        (valid_sched and invs)) and
        budgeted_sc_ntfn_at ntfnptr and active_sc_ntfn_at ntfnptr and
        not_cur_thread tcbptr and has_budget tcbptr\<rbrace>
       do y <- cancel_ipc tcbptr;
          y <- set_thread_state tcbptr Running;
          y <- as_user tcbptr (setRegister badge_register badge);
          y <- maybe_donate_sc tcbptr ntfnptr;
          possible_switch_to tcbptr
       od
       \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: possible_switch_to_valid_sched3)
      apply_trace (wpsimp wp: maybe_donate_sc_valid_ready_qs
                        maybe_donate_sc_valid_release_q
                        maybe_donate_sc_valid_sched_action
                        maybe_donate_sc_ct_not_in_q2
                        maybe_donate_sc_ct_in_cur_domain
                        maybe_donate_sc_active_sc_tcb_at
                        maybe_donate_sc_budget_conditions
                        maybe_donate_sc_valid_blocked_except_set
                        maybe_donate_sc_has_budget
                        hoare_vcg_imp_lift'')
     apply wpsimp
    apply (rule_tac Q="\<lambda>xc s. (valid_sched_except_blocked s \<and> valid_blocked_except_set {tcbptr} s)
                       \<and> not_queued tcbptr s \<and> scheduler_act_not tcbptr s \<and> not_in_release_q tcbptr s
                       \<and> not_cur_thread tcbptr s
                       \<and> st_tcb_at runnable tcbptr s
                       \<and> active_sc_ntfn_at' ntfnptr s \<and> has_budget tcbptr s
                       \<and> budgeted_sc_ntfn_at ntfnptr s"
                    in hoare_strengthen_post[rotated])
     apply (clarsimp)
    apply (rule hoare_vcg_conj_lift)
     apply (rule set_thread_state_break_valid_sched[simplified pred_conj_def])
    apply (wpsimp wp: sts_st_tcb_at')
   apply simp
   apply (wpsimp wp: cancel_ipc_BOR_valid_sched cancel_ipc_BOR_other)
  apply (clarsimp simp:)
  apply (intro conjI; assumption?)
    apply (erule valid_sched_not_runnable_not_queued)
    apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
   apply (erule valid_sched_not_runnable_scheduler_act_not)
   apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
  apply (erule valid_sched_not_runnable_not_in_release_q)
  apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_def obj_at_def)
  done

lemma send_signal_valid_sched:
  "\<lbrace> valid_sched and invs and active_sc_ntfn_at ntfnptr and budgeted_sc_ntfn_at ntfnptr and
      valid_ntfn_q and
      active_and_budgeted_tcb_ntfn_at ntfnptr and
      (\<lambda>s. \<forall>ntfn a. ko_at (Notification ntfn) ntfnptr s \<longrightarrow> ntfn_bound_tcb ntfn = Some a \<longrightarrow> not_cur_thread a s) and
      valid_ntfn_q\<rbrace>
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
           apply (wpsimp wp: send_signal_BOR_helper)
           apply (intro conjI)
            apply assumption
           apply (clarsimp simp: active_and_budgeted_tcb_ntfn_at_def has_budget_def)
          prefer 8
          apply (wpsimp wp: send_signal_WaitingNtfn_helper)
          apply (subgoal_tac "x2 \<noteq> [] \<and> tcb_at (hd x2) s")
           apply (intro conjI)
             apply (subgoal_tac "(ntfnptr, TCBSignal) \<in> state_refs_of s (hd x2)")
              apply (clarsimp simp: pred_tcb_at_eq_commute st_tcb_at_refs_of_rev(5)[symmetric] obj_at_def
                                    state_refs_of_def)
             apply (rule sym_refsE)
              apply (rule invs_sym_refs, simp)
             apply (clarsimp simp: state_refs_of_def obj_at_def)
           apply (fastforce elim: valid_nftn_qD2)
           apply (fastforce elim: valid_nftn_qD1)
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
              apply ((wp possible_switch_to_valid_sched' sts_st_tcb_at' hoare_drop_imps
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
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and valid_sched[wp]: valid_sched
  (simp: wp: hoare_drop_imp hoare_vcg_if_lift2)

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

    apply (clarsimp simp: valid_release_q_def not_in_release_q_def st_tcb_at_kh_def
               etcb_defs active_sc_tcb_at_defs split: option.splits)
    apply (drule_tac x=t in bspec, simp, clarsimp simp: active_sc_tcb_at_defs split: option.splits)
    apply(intro conjI; fastforce)
   apply (clarsimp simp: valid_sched_action_def)
   apply (rule conjI)
    apply (clarsimp simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def active_sc_tcb_at_defs)
   apply (rule conjI; clarsimp simp: scheduler_act_not_def)
   apply (rule_tac x=scp in exI, fastforce)
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_def active_sc_tcb_at_defs split: option.splits)
  apply (drule_tac x=t in spec, clarsimp)
  done

crunches do_nbrecv_failed_transfer
for valid_sched[wp]: valid_sched
  (wp: valid_sched_lift)

lemma as_user_test_sc_refill_max[wp]:
  "\<lbrace>test_sc_refill_max scp\<rbrace> as_user tptr f \<lbrace>\<lambda>_. test_sc_refill_max scp\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def wp: get_object_def)
  by (clarsimp simp: test_sc_refill_max_def dest!: get_tcb_SomeD split: option.splits)

lemma receive_signal_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not thread and not_queued thread and not_in_release_q thread\<rbrace>
     receive_signal thread cap is_blocking \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: receive_signal_def)
  apply (cases cap; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
(*
  apply (wpsimp wp: maybe_donate_sc_valid_sched
                  set_thread_state_not_queued_valid_sched)
  apply (wpsimp wp: maybe_donate_sc_valid_sched
                  set_thread_state_not_queued_valid_sched)
apply (wpsimp wp: maybe_donate_sc_valid_sched)
  apply (wpsimp wp: maybe_donate_sc_valid_sched get_object_wp
   set_simple_ko_test_sc_refill_max set_simple_ko_valid_sched hoare_vcg_conj_lift
   hoare_vcg_all_lift hoare_drop_imp
simp: obj_at_def set_object_def) *)
sorry (* receive_signal_valid_sched *)


(*
crunch valid_sched: schedule_tcb,maybe_return_sc,maybe_donate_sc valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv)

crunch valid_sched: receive_signal valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv mapM_wp)
*)

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
       apply (wp tcb_sched_action_enqueue_not_queued gts_wp| clarsimp | wpc)+
      apply (erule notE, assumption)
     apply (wp reschedule_required_not_queued | simp add: get_ep_queue_def)+
     apply (rule hoare_gen_asm)
     apply (rule_tac S="set queue - {t}" in mapM_x_wp)
      apply (wp tcb_sched_action_enqueue_not_queued gts_wp | wpc | clarsimp)+
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
       apply (wp tcb_sched_action_enqueue_not_queued | clarsimp)+
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

lemma unbind_maybe_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_maybe_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def get_sk_obj_ref_def
         wp: get_simple_ko_wp)

lemma unbind_maybe_notification_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
     unbind_maybe_notification a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_maybe_notification_def get_sk_obj_ref_def maybeM_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def, frule (4) ntfn_bound_tcb_at)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm, frule ko_at_state_refs_ofD, simp)+
   apply (frule_tac P="(=) (Some a)" in ntfn_bound_tcb_at, simp_all add: obj_at_def)[1]
  apply (clarsimp simp: obj_at_def, frule (4) ntfn_bound_tcb_at, clarsimp simp: pred_tcb_at_def obj_at_def)
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

lemma lookup_reply_valid_fault[wp]:
  "\<lbrace>\<top>\<rbrace> lookup_reply -,\<lbrace>\<lambda>rv s::det_state. valid_fault rv\<rbrace>"
  apply (clarsimp simp: lookup_reply_def)
  apply (wpsimp simp: valid_fault_def lookup_cap_def lookup_slot_for_thread_def
 wp: hoare_vcg_conj_lift hoare_vcg_all_lift)
  sorry (* lookup_reply_valid_fault *)

abbreviation ct_schedulable where
  "ct_schedulable s \<equiv> active_sc_tcb_at (cur_thread s) s
      \<and> budget_ready (cur_thread s) s
      \<and> budget_sufficient (cur_thread s) s"

context DetSchedSchedule_AI begin

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active and ct_not_in_release_q and valid_ep_q
      and ct_not_queued and scheduler_act_sane and ct_schedulable\<rbrace>
   handle_recv is_blocking can_reply \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
              cong: if_cong split del: if_split)
  apply (wpsimp wp: get_simple_ko_wp handle_fault_valid_sched
            receive_ipc_valid_sched receive_signal_valid_sched simp: whenE_def get_sk_obj_ref_def
             split_del: if_split)+
     apply (rule hoare_vcg_E_elim)
      apply (wpsimp simp: lookup_cap_def lookup_slot_for_thread_def)
       apply (wp resolve_address_bits_valid_fault2)+
     apply (simp add: valid_fault_def)
     apply (wp hoare_drop_imps hoare_vcg_all_lift_R)
    apply (wpsimp cong: conj_cong | strengthen invs_valid_tcb_ctable_strengthen)+
  apply (auto simp: ct_in_state_def tcb_at_invs objs_valid_tcb_ctable invs_valid_objs)
  done
(*
lemma handle_recv_valid_sched':
  "\<lbrace>invs and valid_sched and ct_active and ct_not_queued and scheduler_act_sane
 and ct_not_in_release_q and valid_ep_q and ct_schedulable\<rbrace>
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
  "\<lbrace> valid_sched and valid_objs and simple_sched_action and (\<lambda>s. sym_refs (state_refs_of s))
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
  "\<lbrace>valid_release_q\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_release_q_def etcb_defs active_sc_tcb_at_defs refill_prop_defs not_in_release_q_def
                  dest!: get_tcb_SomeD split: option.splits)
  apply (intro conjI; clarsimp)
  apply (drule_tac x=t in bspec, simp)
   apply (fastforce simp: st_tcb_at_kh_def st_tcb_at_def active_sc_tcb_at_defs)
  apply (drule_tac x=ta in bspec, simp)
  by (fastforce simp: st_tcb_at_kh_def st_tcb_at_def active_sc_tcb_at_defs)

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
  by (clarsimp simp: is_schedulable_bool_def get_tcb_rev obj_at_def dest!: get_tcb_SomeD split: option.splits)

lemma thread_set_domain_budget_ready[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: is_refill_ready_def pred_tcb_at_def obj_at_def
                    dest!: get_tcb_SomeD split: option.splits; (intro conjI impI)?;
           (clarsimp split: if_split_asm)?)
  by (rule_tac x=scp in exI, fastforce)+

lemma thread_set_domain_budget_sufficient[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: is_refill_sufficient_def pred_tcb_at_def obj_at_def
                    dest!: get_tcb_SomeD split: option.splits; (intro conjI impI)?;
           (clarsimp split: if_split_asm)?)
  by (rule_tac x=scp in exI, fastforce)+

(* FIXME: move to DetSchedInvs_AI *)
lemma is_schedulable_unfold_simp:
  "(is_schedulable_opt t (in_release_queue t s) s = Some True) =
          (st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> \<not> in_release_queue t s)"
  apply (rule iffI; clarsimp simp: is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def
                     split: option.splits dest!: get_tcb_SomeD)
  by (intro conjI allI impI; clarsimp simp: get_tcb_rev)

(* FIXME: move to DetSchedInvs_AI *)
lemma is_schedulable_unfold_neg_simp:
  "\<lbrakk>tcb_at t s\<rbrakk> \<Longrightarrow>
    (is_schedulable_opt t (in_release_queue t s) s = Some False) =
          (\<not> st_tcb_at runnable t s \<or> \<not> active_sc_tcb_at t s \<or> in_release_queue t s)"
  apply (rule iffI;
         clarsimp simp: is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def is_tcb
                   in_release_queue_def not_in_release_q_def split: option.splits dest!: get_tcb_SomeD)
  by (intro allI impI conjI; clarsimp dest!: get_tcb_SomeD simp: get_tcb_rev)

lemma invoke_domain_valid_sched_helper_blocked:
"\<lbrace>valid_sched and not_queued t and not_in_release_q t and tcb_at t
   and scheduler_act_not t and (\<lambda>s. t \<noteq> cur_thread s) and (\<lambda>s. cur = cur_thread s)\<rbrace>
    do  in_release_q <- gets (in_release_queue t);
       sched <- is_schedulable t in_release_q;
       y <- when sched (tcb_sched_action tcb_sched_enqueue t);
       when (t = cur) reschedule_required
    od
    \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_assume_pre)
   apply (clarsimp simp: valid_sched_def valid_blocked_def scheduler_act_not_def)
   apply (drule_tac x=t in spec, clarsimp)
   apply (clarsimp simp: in_release_queue_def is_schedulable_bool_def active_sc_tcb_at_def
      not_in_release_q_def obj_at_def is_tcb get_tcb_rev pred_tcb_at_def
      split: option.splits)
   apply (case_tac "tcb_state tcb"; clarsimp)
  by wpsimp

lemma invoke_domain_valid_sched_helper_in_rdq:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and (\<lambda>s. cur = cur_thread s)
  and not_queued t and not_in_release_q t and (\<lambda>s. t \<noteq> cur_thread s)
  and st_tcb_at runnable t and active_sc_tcb_at t
  and budget_ready t and budget_sufficient t\<rbrace>
    do  in_release_q <- gets (in_release_queue t);
       sched <- is_schedulable t in_release_q;
       y \<leftarrow> when sched (tcb_sched_action tcb_sched_enqueue t);
       when (t = cur) reschedule_required
    od
    \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (wpsimp wp: tcb_sched_action_enqueue_valid_sched)
  by (fastforce simp: not_in_release_q_def in_release_queue_def get_tcb_rev
 is_schedulable_bool_def active_sc_tcb_at_defs not_cur_thread_def split: option.splits)

lemma invoke_domain_valid_sched_helper_in_rlq:
  "\<lbrace>valid_sched and (\<lambda>s. cur = cur_thread s) and tcb_at t
  and not_queued t and in_release_queue t and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace>
    do  in_release_q <- gets (in_release_queue t);
       sched <- is_schedulable t in_release_q;
       y \<leftarrow> when sched (tcb_sched_action tcb_sched_enqueue t);
       when (t = cur) reschedule_required
    od
    \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (case_tac sched; clarsimp)
   apply (rule hoare_assume_pre)
   apply (clarsimp simp: is_schedulable_bool_def obj_at_def is_tcb get_tcb_rev
            split: option.splits)
  by wpsimp

lemma invoke_domain_valid_sched[wp]:
  notes tcb_sched_action_enqueue_valid_sched[wp del]
  shows
  "\<lbrace>valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and (\<lambda>s. t \<noteq> cur_thread s)
                and scheduler_act_not t and valid_idle and ready_or_released\<rbrace>
    invoke_domain t d \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: invoke_domain_def)
  including no_pre
  apply wp
  apply (simp add: set_domain_def)
  apply (rule_tac Q="(\<lambda>s. (valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and (\<lambda>s. t \<noteq> cur_thread s) and
       scheduler_act_not t and valid_idle
      and not_queued t and not_in_release_q t) s \<or>
   ((valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and (\<lambda>s. t \<noteq> cur_thread s) and
      scheduler_act_not t and valid_idle)
     and (\<lambda>s. \<not> not_queued t s) and not_in_release_q t) s \<or>
   ((valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s) and (\<lambda>s. t \<noteq> cur_thread s) and
      scheduler_act_not t and valid_idle)
     and (\<lambda>s. in_release_queue t s) and not_queued t) s)" in hoare_weaken_pre)
   apply (rule_tac Q="\<lambda>_ s. valid_sched s \<or> valid_sched s \<or> valid_sched s" in hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift)
    (* blocked *)
     apply (wpsimp wp: invoke_domain_valid_sched_helper_blocked
      tcb_dequeue_not_queued_gen thread_set_domain_not_idle_valid_sched
      tcb_sched_action_dequeue_valid_sched_not_queued)
    (* in either of the queues *)
    apply (rule hoare_vcg_disj_lift)
    (* in ready_queues *)
     apply (wpsimp wp: invoke_domain_valid_sched_helper_in_rdq
      tcb_sched_action_enqueue_valid_sched
      thread_set_domain_valid_blocked_except
      thread_set_domain_act_not_valid_sched_action
      thread_set_domain_valid_ready_qs_not_q
      thread_set_domain_ct_in_cur_domain tcb_dequeue_not_queued
      thread_set_domain_not_idle_valid_idle_etcb
      tcb_sched_action_dequeue_valid_ready_qs
      tcb_sched_action_dequeue_valid_blocked_except)
     apply (clarsimp simp: valid_sched_def not_cur_thread_def valid_ready_qs_def
      etcb_defs not_queued_def)
    (* in release_queue *)
    apply (wpsimp wp: invoke_domain_valid_sched_helper_in_rlq
      thread_set_domain_not_idle_valid_sched tcb_dequeue_not_queued_gen
      tcb_sched_action_dequeue_valid_sched_not_queued)
   apply simp
  by (case_tac "not_queued t s"; case_tac "not_in_release_q t s";
      clarsimp simp: in_release_queue_def not_in_release_q_def not_queued_def ready_or_released_def)

(*
lemma idle_not_reply_cap:
  "\<lbrakk> valid_idle s; cte_wp_at ((=) (ReplyCap r)) p s \<rbrakk> \<Longrightarrow> r \<noteq> idle_thread s"
  apply (drule_tac p=p in valid_reply_caps_of_stateD)
   apply (simp add: caps_of_state_def cte_wp_at_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done*)

context DetSchedSchedule_AI begin

lemma perform_invocation_valid_sched[wp]:
  "\<lbrace>invs and valid_invocation i and ct_active and scheduler_act_sane and valid_sched
        and valid_ep_q and ct_not_queued and ct_not_in_release_q and ct_schedulable\<rbrace>
     perform_invocation block call can_donate i
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (cases i;
         wpsimp wp: invoke_untyped_valid_sched send_ipc_valid_sched send_signal_valid_sched
                    do_reply_transfer_valid_sched invoke_tcb_valid_sched
                    invoke_irq_control_valid_sched arch_invoke_irq_control_valid_sched'
                    invoke_cnode_valid_sched
              simp: invs_valid_idle invs_valid_objs)
apply (clarsimp simp: ct_in_state_def)

(*          apply ((wp invoke_untyped_valid_sched send_ipc_valid_sched | clarsimp)+)[3]
         apply (clarsimp simp: ct_in_state_def)
        apply (wp invoke_cnode_valid_sched send_ipc_valid_sched invoke_domain_valid_sched
             | simp add: invs_valid_objs invs_valid_idle invs_valid_reply_caps
             | clarsimp simp: ct_in_state_def)+
  done*)
sorry (* perform_invocation_valid_sched *)

end

context DetSchedSchedule_AI begin
lemma handle_invocation_valid_sched:
  "\<lbrace>invs and valid_sched and ct_active and valid_ep_q and ct_not_queued and ct_not_in_release_q and
    (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_schedulable\<rbrace>
     handle_invocation calling blocking can_donate cptr
   \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid handle_fault_valid_sched | wpc)+
                apply (wp set_thread_state_runnable_valid_sched)[1]
               apply wp+
         apply (wp gts_wp hoare_vcg_all_lift)
        apply (rule_tac Q="\<lambda>_. valid_sched" and E="\<lambda>_. valid_sched" in hoare_post_impErr)
          apply wp
         apply ((clarsimp simp: st_tcb_at_def obj_at_def)+)[2]
       apply (wp ct_in_state_set set_thread_state_runnable_valid_sched set_thread_state_ct_valid_ep_q_inv
            hoare_vcg_E_conj | simp add: split_def if_apply_def2 split del: if_split)+
  apply (auto simp: ct_in_state_def valid_sched_def ct_not_in_q_def valid_ready_qs_def not_queued_def runnable_eq_active elim: st_tcb_ex_cap)
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

crunch weak_valid_sched_action[wp]: reply_cancel_ipc weak_valid_sched_action
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

lemma assert_false:"\<lbrace>\<lambda>s. \<not> P\<rbrace> assert P \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply wp
  apply simp
  done
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

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_interrupt irq \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  apply (wpsimp wp: get_cap_wp hoare_drop_imps hoare_vcg_all_lift send_signal_valid_sched | rule conjI)+
  sorry (* handle_interrupt_valid_sched *)

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
refill_split_check_valid_sched (* not proved *)
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


crunches transfer_caps_loop,check_budget_restart
for cur_thread[wp]: "\<lambda>s::det_state. P (cur_thread s)"
  (wp: transfer_caps_loop_pres mapM_wp' maybeM_wp hoare_drop_imps simp: Let_def)

crunches tcb_release_enqueue
for not_queued[wp]: "not_queued t"
and simple_sched_action[wp]: simple_sched_action
  (wp: hoare_drop_imp mapM_wp')

lemma postpone_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> postpone scptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: postpone_def)
  apply (wpsimp simp: tcb_sched_action_def get_sc_obj_ref_def thread_get_def wp: get_sched_context_wp hoare_drop_imp)
  by (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def split: option.splits)

lemma end_timeslice_not_queued[wp]:
  "\<lbrace>not_queued t and ct_active and (\<lambda>s. cur_thread s \<noteq> t) and scheduler_act_not t\<rbrace>
     end_timeslice canTimeout \<lbrace>\<lambda>_. not_queued t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: end_timeslice_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac "ct=it"; clarsimp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (rule hoare_if)
   apply wpsimp
  apply (rule hoare_if)
   apply (wpsimp simp: not_cur_thread_def tcb_sched_action_def thread_get_def)
   apply (clarsimp simp: not_queued_def tcb_sched_append_def)
  apply wpsimp
  done

(* FIXME: move *)
lemma ct_active_machine_op[wp]:
  "\<lbrace>ct_active\<rbrace> do_machine_op f \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
  by wp+

(* FIXME: Move to Arch *)
lemma getCurrentTime_valid_sched[wp]:
  "valid valid_sched (do_machine_op getCurrentTime) (\<lambda>_. valid_sched::det_state \<Rightarrow> _)"
  apply (simp add: ARM.getCurrentTime_def modify_def)
  by (wpsimp wp: do_machine_op_valid_sched simp: modify_def)

crunches update_time_stamp
for scheduler_action[wp]: "\<lambda>s::det_state. P (scheduler_action s)"
and cur_thread[wp]: "\<lambda>s::det_state. P (cur_thread s)"
and ct_active[wp]: "ct_active::det_state \<Rightarrow> _"
and pred_tcb_at[wp]: "pred_tcb_at p P t::det_state \<Rightarrow> _"
and pred_tcb_at_ct[wp]: "\<lambda>s::det_state. pred_tcb_at p P (cur_thread s) s"
  (wp: crunch_wps ARM.getCurrentTime_def)

lemma ct_active_is_original_cap_update[simp]:
  "ct_active(s\<lparr>is_original_cap := param_a\<rparr>) = ct_active s"
  by (clarsimp simp: ct_in_state_def)

lemma ct_active_cdt_update[simp]:
  "ct_active(s\<lparr>cdt := param_a\<rparr>) = ct_active s"
  by (clarsimp simp: ct_in_state_def)

lemma set_cap_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     set_cap cap slot
       \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (wpsimp simp: ct_in_state_def)
  by (rule hoare_lift_Pf[where f=cur_thread]; wp)

crunches cap_insert,set_extra_badge
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

crunches lookup_ipc_buffer,do_normal_transfer,do_fault_transfer
for ct_active[wp]: "ct_active::det_state \<Rightarrow> _"
 (simp: zipWithM_x_mapM wp: mapM_wp' transfer_caps_loop_pres as_user_ct_in_state)

lemma sts_not_cur:
  "\<lbrace>\<lambda>s. st_tcb_at active (cur_thread s) s \<and> tptr \<noteq> cur_thread s\<rbrace>
     set_thread_state tptr Inactive
       \<lbrace>\<lambda>_ s. st_tcb_at active (cur_thread s) s\<rbrace>"
  apply (rule hoare_lift_Pf2[where f=cur_thread])
  by (wp sts_st_tcb_at_other, clarsimp) wp

lemma reply_unlink_tcb_ct_active[wp]:
  "\<lbrace>ct_active and (\<lambda>s. reply_tcb_reply_at (\<lambda>p. \<forall>rp. p = Some rp \<and> rp \<noteq> cur_thread s) r s)\<rbrace>
     reply_unlink_tcb r
       \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def assert_def assert_opt_def)
  apply (wpsimp simp: ct_in_state_def wp: sts_not_cur)
       apply (rule hoare_lift_Pf2[where f=cur_thread])
        apply (wp set_simple_ko_pred_tcb_at, wp)
      apply wpsimp
     apply (wpsimp wp: gts_wp get_simple_ko_wp)+
  by (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def ct_in_state_def)


lemma do_ipc_transfer_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     do_ipc_transfer sender ep badge grant receiver
       \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def)

(* do we need these?
lemma send_ipc_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     send_ipc True False badge True False thread epptr
       \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
   apply (clarsimp simp: send_ipc_def)
  by (wpsimp simp: send_ipc_def set_simple_ko_def a_type_def partial_inv_def
      wp: set_object_wp get_object_wp sts_st_tcb_at' hoare_vcg_all_lift hoare_drop_imp)

lemma send_fault_ipc_ct_active_for_timeout[wp]:
  "\<lbrace>ct_active\<rbrace>
     send_fault_ipc tptr ep f False \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
   apply (clarsimp simp: send_fault_ipc_def)
  by (wpsimp simp: send_fault_ipc_def wp: thread_set_fault_ct_active_wp)
thm handle_timeout_def end_timeslice_def postpone_def
lemma handle_timeout_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     handle_timeout tptr f \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: handle_timeout_def)

lemma postpone_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     postpone scp \<lbrace>\<lambda>_.  ct_active::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: postpone_def wp: hoare_drop_imp)

lemma end_timeslice_ct_active:
  "\<lbrace>ct_active\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: end_timeslice_def)

lemma charge_budget_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: charge_budget_def)
  by (wpsimp simp: charge_budget_def Let_def)

lemma check_budget_ct_active:
  "\<lbrace>ct_active\<rbrace> check_budget \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  by (wpsimp wp: hoare_vcg_if_lift2 get_sched_context_wp hoare_vcg_all_lift hoare_drop_imp)

*)

lemma charge_budget_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: charge_budget_def)
(*  apply (wpsimp wp: reschedule_preserves_valid_shed update_sc_consumed_valid_sched
update_sched_context_valid_sched get_refills_wp refill_budget_check_valid_sched hoare_drop_imp
 simp: set_refills_def Let_def)
apply (intro conjI; clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
active_sc_tcb_at_defs valid_ready_qs_def is_refill_sufficient_def is_refill_ready_def etcb_defs
split: option.splits)
apply (intro conjI; clarsimp?)
apply fastforce
defer
apply fastforce
apply (clarsimp simp: sufficient_refills_def refills_capacity_def)*)
sorry (* charge_budget_valid_sched *)

lemma check_budget_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> check_budget \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (wpsimp wp: get_sched_context_wp
                    hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)
  done

lemma reschedule_required_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     reschedule_required \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma tcb_release_enqueue_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace> tcb_release_enqueue t' \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
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

lemma make_fault_msg_active_sc_tcb_at[wp]:
"\<lbrace>active_sc_tcb_at t\<rbrace> make_fault_msg f t' \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  by (case_tac f; wpsimp split_del: if_split)

lemma do_fault_transfer_active_sc_tcb_at[wp]:
"\<lbrace>active_sc_tcb_at t\<rbrace> do_fault_transfer badge sender receiver buf \<lbrace>\<lambda>_. active_sc_tcb_at t::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: do_fault_transfer_def)
  by (wpsimp wp: make_fault_msg_active_sc_tcb_at simp: thread_get_def)


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

lemma update_sc_consumed_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     update_sched_context scptr (\<lambda>sc. sc\<lparr>sc_consumed := f sc\<rparr>)
      \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  by (intro conjI impI, clarsimp, rule_tac x=scp in exI, fastforce)

lemma update_sc_consumed_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     update_sched_context scptr (\<lambda>sc. sc\<lparr>sc_consumed := (f sc)\<rparr>) \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]) wpsimp+

lemma update_sc_refills_active_sc_tcb_at[wp]:
  "\<lbrace>active_sc_tcb_at t\<rbrace>
     update_sched_context scptr (\<lambda>sc. sc\<lparr>sc_refills := (f sc)\<rparr>) \<lbrace>\<lambda>_. active_sc_tcb_at t\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  by (intro conjI impI, clarsimp, rule_tac x=scp in exI, fastforce)

lemma update_sc_refills_active_sc_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
     update_sched_context scptr (\<lambda>sc. sc\<lparr>sc_refills := (f sc)\<rparr>) \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp simp: active_sc_tcb_at_defs split: option.splits)
  by (intro conjI impI, clarsimp, rule_tac x=scp in exI, fastforce)

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


lemma refill_split_check_active_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace>
     refill_split_check sc_ptr usage \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  by (wpsimp simp: Let_def refill_split_check_def split_del: if_split)

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


(* when check_budget returns True, it has not called charge_budget. Hence the
thread_state remains unchanged *)

lemma check_budget_true_st_tcb_at:
  "\<lbrace> \<lambda>s. st_tcb_at P t s \<rbrace> check_budget \<lbrace> \<lambda>rv s. rv \<longrightarrow>  st_tcb_at P t s\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ refill_capacity_sp])
  apply (rule hoare_if)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_if)
    by wpsimp+

lemma check_budget_restart_st_tcb_at:
  "\<lbrace> \<lambda>s. st_tcb_at P t s \<rbrace> check_budget_restart \<lbrace> \<lambda>rv s. rv \<longrightarrow> st_tcb_at P t s\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (rule hoare_seq_ext[OF _ check_budget_true_st_tcb_at])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_vcg_if_lift)
  done


lemma check_budget_restart_valid_sched:
  "\<lbrace>valid_sched\<rbrace> check_budget_restart \<lbrace>\<lambda>rv s::det_state. rv \<longrightarrow> valid_sched s\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (wpsimp wp: gts_wp hoare_vcg_all_lift)
  by (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2) simp

(* not quite true
lemma check_budget_restart_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> check_budget_restart \<lbrace>\<lambda>_. ct_active::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  by (wpsi mp simp: check_budget_restart_def set_thread_state_def set_object_def
                 wp: hoare_drop_imp hoare_vcg_if_lift2
        | rule hoare_strengthen_post[where Q="\<lambda>_. ct_active"]
        | simp add: ct_in_state_def pred_tcb_at_def obj_at_def)+

*)

(* when check_budget returns True, it has not called reschedule_required. Hence the
scheduler_action remains unchanged *)

lemma check_budget_true_sched_action:
  "\<lbrace> \<lambda>s. P (scheduler_action s) \<rbrace> check_budget \<lbrace> \<lambda>rv s. rv \<longrightarrow> P (scheduler_action s)\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ refill_capacity_sp])
  apply (rule hoare_if)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_if)
    by wpsimp+

lemma check_budget_restart_sched_action:
  "\<lbrace> \<lambda>s. P (scheduler_action s) \<rbrace> check_budget_restart \<lbrace> \<lambda>rv s. rv \<longrightarrow> P (scheduler_action s)\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (rule hoare_seq_ext[OF _ check_budget_true_sched_action])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_vcg_if_lift)
  done


(* FIXME: Move to Arch *)
lemma getCurrentTime_invs[wp]:
  "valid invs (do_machine_op getCurrentTime) (\<lambda>_. invs)"
  apply (simp add: ARM.getCurrentTime_def modify_def)
  apply (wpsimp wp: dmo_invs simp: modify_def)
  by (simp add: do_machine_op_def modify_def in_get bind_assoc get_def put_def gets_def in_bind
                   split_def select_f_returns in_return)

lemma update_time_stamp_invs[wp]:
  "\<lbrace>invs\<rbrace> update_time_stamp \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: update_time_stamp_def)

lemma handle_yield_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> handle_yield \<lbrace>\<lambda>rv. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: handle_yield_def)


(* when check_budget returns True, it has not called reschedule_required. Hence the
scheduler_action remains unchanged *)
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
      and (\<lambda>s. bound_sc_tcb_at bound (cur_thread s) s) (*and simple_sched_action*)\<rbrace>
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
            check_budget_true_sched_action[where P="(=) resume_cur_thread"]
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
  by (wp | simp)+

crunches handle_interrupt,check_budget
for cur_tcb[wp]: "cur_tcb::det_state \<Rightarrow> _"
 (wp: crunch_wps get_simple_ko_wp hoare_drop_imp hoare_vcg_all_lift maybeM_wp
  simp: Let_def crunch_simps)

lemma call_kernel_valid_sched_helper:
  "\<lbrace>\<lambda>s. (valid_sched and invs and
         (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)) s \<and>
        invs s \<and> bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   check_budget
   \<lbrace>\<lambda>_ s::det_state. (valid_sched and invs and
             (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)) s \<and>
            invs s\<rbrace>"
   apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def) (* FIXME RT *)
   by (wpsimp wp: hoare_vcg_conj_lift reschedule_preserves_valid_shed get_sched_context_wp
                  hoare_drop_imps hoare_vcg_all_lift charge_budget_invs)

lemma call_kernel_valid_sched:
  "\<lbrace>\<lambda>s. invs s \<and> valid_sched s \<and> (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) s \<and> (ct_active or ct_idle) s
        \<and> (\<lambda>s. scheduler_action s = resume_cur_thread) s \<and> bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. valid_sched::det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp schedule_valid_sched activate_thread_valid_sched | simp)+
      apply (rule_tac Q="\<lambda>rv. invs" in hoare_strengthen_post)
       apply wp
      apply (erule invs_valid_idle)
     apply (wp call_kernel_valid_sched_helper)
    apply (rule hoare_strengthen_post
      [where Q="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> valid_sched s \<and> invs s \<and>
                             bound_sc_tcb_at bound (cur_thread s) s"])
     apply (wpsimp wp: getActiveIRQ_neq_non_kernel)
    apply auto[1]
   apply (rule_tac Q="\<lambda>rv s. valid_sched s \<and> invs s" and
      E="\<lambda>rv s. valid_sched s \<and> invs s" in hoare_post_impErr)
     apply (rule valid_validE)
     apply (wp handle_event_valid_sched)
    apply clarsimp+
  subgoal for s
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

end

end

