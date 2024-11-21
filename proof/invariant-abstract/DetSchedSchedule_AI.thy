(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedSchedule_AI
imports ArchDetSchedDomainTime_AI
begin

crunch do_machine_op
  for ct_not_in_q[wp]: "ct_not_in_q"

lemma set_tcb_queue_wp[wp]: "\<lbrace>\<lambda>s. P (ready_queues_update (\<lambda>_ t' p. if t' = t \<and> p = prio then queue else ready_queues s t' p) s)\<rbrace> set_tcb_queue t prio queue \<lbrace>\<lambda>_. P\<rbrace>"
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

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 resume_cur_thread kh"
  "weak_valid_sched_action_2 choose_new_thread kh"
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
  "valid_sched_action_2 choose_new_thread ekh kh ct cdom"
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

lemma tcb_sched_action_enqueue_valid_queues[wp]:
  "\<lbrace>valid_queues and st_tcb_at runnable thread\<rbrace>
   tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: valid_queues_def2 etcb_at_def tcb_sched_enqueue_def is_etcb_at_def
                 split: option.split
                 dest!: ko_at_etcbD)
  done

lemma tcb_sched_action_append_valid_queues[wp]:
  "\<lbrace>valid_queues and st_tcb_at runnable thread\<rbrace>
     tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: valid_queues_def2 etcb_at_def tcb_sched_append_def is_etcb_at_def
                 split: option.split
                 dest!: ko_at_etcbD)
  done

lemma tcb_sched_action_dequeue_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> tcb_sched_action tcb_sched_dequeue thread \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: valid_queues_def2 etcb_at_def tcb_sched_dequeue_def
         split: option.splits)
  apply blast
  done

lemma tcb_sched_action_enqueue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_enqueue_def not_queued_def
         split: option.splits)
  done

lemma tcb_sched_action_append_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and not_cur_thread thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
     \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: ct_not_in_q_def not_cur_thread_def etcb_at_def
                        tcb_sched_append_def not_queued_def
                  split: option.splits)
  done

lemma tcb_sched_action_dequeue_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (fastforce simp: ct_not_in_q_def etcb_at_def tcb_sched_dequeue_def
                         not_queued_def
                   split: option.splits)
  done

crunch tcb_sched_action
  for is_activatable[wp]: "is_activatable t"

crunch tcb_sched_action
  for weak_valid_sched_action[wp]: "weak_valid_sched_action"

crunch tcb_sched_action
  for valid_sched_action[wp]: valid_sched_action

crunch tcb_sched_action
  for ct_in_cur_domain[wp]: ct_in_cur_domain

lemma tcb_sched_action_enqueue_valid_blocked:
  "\<lbrace>valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "t=thread")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  apply clarsimp
  apply (case_tac "t=thread")
   apply force
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply force
  done

lemma tcb_sched_action_append_valid_blocked:
  "\<lbrace>valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_append_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "t=thread")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  apply clarsimp
  apply (case_tac "t=thread")
   apply force
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply force
  done

lemma tcb_sched_action_dequeue_valid_blocked:
  "\<lbrace>valid_blocked and st_tcb_at (\<lambda>st. \<not> active st) thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_blocked_def split: option.splits)
  apply (case_tac "t=thread")
   apply simp
   apply (force simp: st_tcb_at_def obj_at_def)
  apply (erule_tac x=t in allE)
  apply force
  done

lemma tcb_sched_action_dequeue_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (case_tac "t=thread")
   apply simp
  apply (erule_tac x=t in allE)
  apply force
  done

abbreviation valid_sched_except_blocked_2 where
  "valid_sched_except_blocked_2 queues ekh sa cdom kh ct it \<equiv>
      valid_queues_2 queues ekh kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_2 sa ekh kh ct cdom \<and> ct_in_cur_domain_2 ct it sa cdom ekh \<and> valid_idle_etcb_2 ekh"

abbreviation valid_sched_except_blocked :: "'z state \<Rightarrow> bool" where
  "valid_sched_except_blocked s \<equiv> valid_sched_except_blocked_2 (ready_queues s) (etcbs_of s) (scheduler_action s) (cur_domain s) (kheap s) (cur_thread s) (idle_thread s)"

declare valid_idle_etcb_lift[wp]

lemma tcb_sched_action_enqueue_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and not_cur_thread thread and valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
by (simp add: valid_sched_def | wp tcb_sched_action_enqueue_valid_blocked)+

lemma tcb_sched_action_append_valid_sched[wp]:
  "\<lbrace>valid_sched_except_blocked and st_tcb_at runnable thread and not_cur_thread thread and valid_blocked_except thread\<rbrace>
      tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_sched_action_append_valid_blocked)+

lemma tcb_sched_action_dequeue_valid_sched_not_runnable:
  "\<lbrace>valid_sched and st_tcb_at (\<lambda>st. \<not> active st) thread\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_sched_action_dequeue_valid_blocked)+

lemma tcb_sched_action_dequeue_valid_sched_except_blocked:
  "\<lbrace>valid_sched\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  by (simp add: valid_sched_def | wp tcb_sched_action_dequeue_valid_blocked_except)+

crunch set_scheduler_action
  for valid_queues[wp]: "valid_queues"

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

crunch set_scheduler_action
  for etcb_at[wp]: "etcb_at P t"

lemma set_scheduler_action_rct_valid_sched:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and simple_sched_action\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp set_scheduler_action_rct_valid_blocked)+

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

lemma set_scheduler_action_cnt_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread  \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply clarsimp
  apply (erule_tac x=t in allE)
  apply (erule impCE)
   apply force
  apply (erule_tac x=st in allE)
  apply (force simp: not_queued_def)
  done

lemma set_scheduler_action_cnt_valid_blocked_except:
  "\<lbrace>valid_blocked_except target and (\<lambda>s. \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread  \<lbrace>\<lambda>_. valid_blocked_except target\<rbrace>"
  apply (simp add: valid_blocked_except_def, wp set_scheduler_action_wp)
  apply clarsimp
  apply (erule_tac x=t in allE)
  apply (erule impCE)
   apply force
  by (fastforce simp: not_queued_def)

lemma set_scheduler_action_cnt_weak_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def simple_sched_action_def split: scheduler_action.splits | wp set_scheduler_action_cnt_valid_blocked)+

lemma reschedule_required_valid_queues[wp]:
  "\<lbrace>valid_queues and weak_valid_sched_action\<rbrace>
      reschedule_required
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: reschedule_required_def | wp | wpc)+
  apply (simp add: weak_valid_sched_action_def)
  done

lemma reschedule_required_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_is_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_weak_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  by (simp add: reschedule_required_def, wp)


lemma tcb_sched_action_enqueue_valid_blocked_except:
  "\<lbrace>valid_blocked_except thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread'
   \<lbrace>\<lambda>_. valid_blocked_except thread \<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "t=thread")
    apply force
   apply (erule_tac x=t in allE)
   apply clarsimp
   apply force
  apply clarsimp
  apply (case_tac "t=thread")
   apply force
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply force
  done

lemma reschedule_required_valid_sched_action[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def reschedule_required_def)
  apply (wp set_scheduler_action_wp | simp)+
  done

lemma reschedule_required_ct_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma reschedule_required_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: reschedule_required_def | wp set_scheduler_action_cnt_valid_blocked tcb_sched_action_enqueue_valid_blocked hoare_vcg_all_lift | wpc)+
    apply (simp add: tcb_sched_action_def)
    apply wp+
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply (force simp: etcb_at_def tcb_sched_enqueue_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply clarsimp
  done

lemma reschedule_required_valid_blocked_except:
  "\<lbrace>valid_blocked_except target\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_blocked_except target\<rbrace>"
  apply (simp add: reschedule_required_def | wp  set_scheduler_action_cnt_valid_blocked_except tcb_sched_action_enqueue_valid_blocked_except hoare_vcg_all_lift | wpc)+
    apply (simp add: tcb_sched_action_def)
    apply wp+
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply (force simp: etcb_at_def tcb_sched_enqueue_def valid_blocked_except_def split: option.splits)
  apply clarsimp
  done

crunch reschedule_required
  for etcb_at[wp]: "etcb_at P t"

lemma reschedule_required_valid_sched:
  "\<lbrace>valid_queues and weak_valid_sched_action and valid_blocked and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+

lemma reschedule_required_valid_sched_cur_thread:
  "\<lbrace>(\<lambda>s. target = cur_thread s) and valid_queues and weak_valid_sched_action and valid_blocked_except target and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+
  apply (clarsimp simp: valid_blocked_except_def valid_blocked_def)
  done

lemma get_tcb_st_tcb_at:
  "get_tcb t s = Some y \<Longrightarrow> st_tcb_at \<top> t s"
  apply (simp add: get_tcb_def pred_tcb_at_def obj_at_def
              split: option.splits kernel_object.splits)
  done

lemma st_tcb_at_kh_if_split:
  "st_tcb_at_kh P ptr (\<lambda>t. if t = ref then x else kh t)
     = (if ptr = ref then (\<exists>tcb. x = Some (TCB tcb) \<and> P (tcb_state tcb))
        else st_tcb_at_kh P ptr kh)"
  by (fastforce simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def)

crunch set_thread_state_act
  for valid_queues[wp]: valid_queues

lemma etcbs_of_update_unrelated:
  "\<lbrakk>kh ref = Some (TCB tcb); etcb_of tcb = etcb_of tcb'\<rbrakk> \<Longrightarrow>
    etcbs_of' (\<lambda>r. if r = ref then Some (TCB tcb') else kh r) = etcbs_of' kh"
  by (auto simp: etcbs_of'_def)

lemma etcbs_of_update_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
   etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_state_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma set_thread_state_runnable_valid_queues:
  "\<lbrace>valid_queues and K (runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_object_def get_object_def)
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  done

lemma etcbs_of_update_bound_notification[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
   etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_bound_notification_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma set_bound_notification_valid_queues:
  "\<lbrace>valid_queues\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2)
  done

lemma set_thread_state_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def | wp gts_wp)+
  done

lemma set_bound_notification_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def | wp)+
  done

lemma set_thread_state_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def |
         wp set_scheduler_action_wp gts_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split
                        pred_tcb_at_def obj_at_def)
  done

lemma set_bound_notification_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_bound_notification ref ntfn
   \<lbrace>\<lambda>_ s. is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_thread_state_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def | wp gts_wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split)
  done

lemma set_thread_state_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def
                   | wp set_scheduler_action_wp gts_wp)+
  done

lemma set_bound_notification_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_bound_notification ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def | wp set_scheduler_action_wp gbn_wp)+
  done

lemma set_bound_notification_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action\<rbrace>
      set_bound_notification ref ntfnptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                        st_tcb_def2)
  done

lemma set_thread_state_runnable_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def
        | wp set_thread_state_runnable_weak_valid_sched_action)+
  done

lemma set_thread_state_cur_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     set_thread_state ref ts \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def |
        wp set_scheduler_action_wp gts_wp)+
  done

lemma set_thread_state_schact_is_rct:
  "\<lbrace>schact_is_rct and (\<lambda>s. ref = cur_thread s \<longrightarrow> runnable ts )\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. schact_is_rct\<rbrace>"
  unfolding set_thread_state_def
  apply (clarsimp simp: set_thread_state_act_def)
  apply (wpsimp wp: set_object_wp gts_wp simp: set_scheduler_action_def)
  apply (clarsimp simp: schact_is_rct_def st_tcb_at_def obj_at_def)
  done

lemma set_bound_notification_cur_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     set_bound_notification ref ts \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def |
        wp set_scheduler_action_wp gbn_wp)+
  done

crunch set_thread_state, set_bound_notification
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  (wp: set_object_wp)

lemma set_thread_state_runnable_valid_sched_except_blocked:
  "\<lbrace>valid_sched and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (simp add: valid_sched_def | wp set_thread_state_runnable_valid_queues
                                        set_thread_state_runnable_valid_sched_action)+
  done

lemma set_bound_notification_valid_sched_action:
  "\<lbrace>valid_sched_action\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_bound_notification_weak_valid_sched_action)+
  done

lemma set_bound_notification_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_bound_notification t ntfn \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def get_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  apply (simp only: st_tcb_at_kh_if_split)
  apply (simp add: st_tcb_def2 split: if_split_asm)
  done

lemma set_bound_notification_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp set_bound_notification_valid_queues
                                        set_bound_notification_valid_sched_action)+
  done

lemma valid_blocked_valid_blocked_except[simp]:
  "valid_blocked s \<Longrightarrow> valid_blocked_except t s"
  by (simp add: valid_blocked_def valid_blocked_except_def)

lemma set_thread_state_valid_blocked_except:
  "\<lbrace>valid_blocked\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked_except ref\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wp gts_wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def st_tcb_at_def obj_at_def)
  done

(* as user schedule invariants *)

lemma as_user_valid_queues[wp]: "\<lbrace>valid_queues\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2)
  apply (drule get_tcb_SomeD, auto)
  done

lemma as_user_weak_valid_sched_action[wp]: "\<lbrace>weak_valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (drule get_tcb_SomeD, auto)

lemma as_user_is_activatable[wp]: "\<lbrace>is_activatable t\<rbrace> as_user ptr s \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (drule get_tcb_SomeD, auto)

lemma as_user_valid_sched_action[wp]: "\<lbrace>valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  supply etcbs_of_update_unrelated[simp]
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: valid_sched_action_def st_tcb_at_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: is_activatable_def st_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
   apply (drule get_tcb_SomeD, clarsimp)
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
  apply (drule get_tcb_SomeD, clarsimp)
  done

lemma as_user_etcbs_of[wp]:
  "as_user ptr s \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def wp: get_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp: etcbs_of_update_unrelated)
  done

lemma as_user_ct_in_cur_domain[wp]:
  "as_user ptr s \<lbrace>ct_in_cur_domain\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def wp: get_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp: etcbs_of_update_unrelated)
  done

lemma as_user_valid_blocked[wp]: "\<lbrace>valid_blocked\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=ptr in spec)
  by (drule get_tcb_SomeD, auto)

definition ct_in_q where
  "ct_in_q s \<equiv> st_tcb_at runnable (cur_thread s) s \<longrightarrow> (\<exists>d p. cur_thread s \<in> set (ready_queues s d p))"

locale DetSchedSchedule_AI =
  assumes arch_switch_to_idle_thread_valid_queues'[wp]:
    "\<lbrace>valid_queues\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_queues :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_queues'[wp]:
    "\<And>t. \<lbrace>valid_queues\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_queues :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_idle_thread_weak_valid_sched_action'[wp]:
    "\<lbrace>weak_valid_sched_action\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. weak_valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_weak_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>weak_valid_sched_action\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. weak_valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_ct_not_in_q[wp]:
    "\<lbrace>valid_queues and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_valid_sched_action[wp]:
    "\<lbrace>valid_sched_action and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_ct_in_cur_domain[wp]:
    "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_is_activatable'[wp]:
    "\<And>t t'. \<lbrace>is_activatable t'\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. is_activatable t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>valid_sched_action\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_ct_in_cur_domain_2[wp]:
    "\<And>t' t.
      \<lbrace>\<lambda>s. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
        arch_switch_to_thread t
      \<lbrace>\<lambda>_ s::det_state. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>"
  assumes arch_switch_to_thread_valid_blocked[wp]:
    "\<And>t. \<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_blocked and ct_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_etcbs_of[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (etcbs_of s)\<rbrace>"
assumes arch_switch_to_thread_cur_domain[wp]:
    "\<And>P t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (cur_domain s)\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_idle[wp]:
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes switch_to_idle_thread_ct_not_queued[wp]:
    "\<lbrace>valid_queues  and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  assumes switch_to_idle_thread_valid_blocked[wp]:
    "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_switch_to_thread_exst'[wp]:
    "\<And>P t. \<lbrace>\<lambda>s. P (exst s :: det_ext)\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>rv s. P (exst s)\<rbrace>"
  assumes stit_activatable':
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  assumes arch_switch_to_idle_thread_etcb_at'[wp]:
    "\<And>P t. \<lbrace>etcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. etcb_at P t :: det_state \<Rightarrow> _\<rbrace>"
  assumes switch_to_idle_thread_cur_thread_idle_thread [wp]:
    "\<lbrace>\<top> :: det_ext state \<Rightarrow> bool\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  assumes arch_finalise_cap_ct_not_in_q'[wp]:
    "\<And>acap final. \<lbrace>ct_not_in_q\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_simple_sched_action'[wp]:
    "\<And>acap final. \<lbrace>simple_sched_action\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_valid_sched'[wp]:
    "\<And>acap final. \<lbrace>valid_sched\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_valid_idle[wp]:
    "\<And>target. \<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace>
                   arch_post_cap_deletion target
                  \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes handle_arch_fault_reply_valid_sched'[wp]:
    "\<And>f t x y. \<lbrace>valid_sched\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes activate_thread_valid_sched:
    "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_perform_invocation_valid_sched[wp]:
    "\<And>i.
      \<lbrace>invs and valid_sched and ct_active and valid_arch_inv i\<rbrace>
        arch_perform_invocation i
      \<lbrace>\<lambda>_.valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_invoke_irq_control_valid_sched'[wp]:
    "\<And>i. \<lbrace>valid_sched\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_valid_sched'[wp]:
    "\<And>t f. \<lbrace>valid_sched\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_not_queued'[wp]:
    "\<And>t' t f. \<lbrace>not_queued t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. not_queued t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_vm_fault_scheduler_act_not'[wp]:
    "\<And>t' t f. \<lbrace>scheduler_act_not t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. scheduler_act_not t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_not_queued'[wp]:
    "\<And>t' f t x y. \<lbrace>not_queued t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. not_queued t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_scheduler_act_not'[wp]:
    "\<And>t' f t x y. \<lbrace>scheduler_act_not t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. scheduler_act_not t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_arch_fault_reply_cur'[wp]:
    "\<And>f t x y. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
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
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_activate_idle_thread t \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes arch_switch_to_thread_valid_list'[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_list'[wp]:
    "\<lbrace>valid_list\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes prepare_thread_delete_idel_thread[wp] :
    "\<And>t. prepare_thread_delete t \<lbrace>\<lambda>(s:: det_ext state). P (idle_thread s)\<rbrace>"
  assumes prepare_thread_delete_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_simple_sched_action'[wp]:
    "\<And>t. \<lbrace>simple_sched_action\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes prepare_thread_delete_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_not_cur_thread[wp] :
    "\<And>ft t t'. make_arch_fault_msg ft t \<lbrace>not_cur_thread t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_valid_sched[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes make_fault_arch_msg_scheduler_action[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes make_fault_arch_msg_ready_queues[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_get_sanitise_register_info_not_cur_thread[wp] :
    "\<And>ft t'. arch_get_sanitise_register_info ft \<lbrace>not_cur_thread t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_sched[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_get_sanitise_register_info_scheduler_action[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes arch_get_sanitise_register_info_ready_queues[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_get_sanitise_register_info_cur'[wp]:
    "\<And>f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_get_sanitise_register_info f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_post_modify_registers_not_cur_thread[wp] :
    "\<And>c ft t'. arch_post_modify_registers c ft \<lbrace>not_cur_thread t' :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_valid_sched[wp] :
    "\<And>c ft. arch_post_modify_registers c ft \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_modify_registers_scheduler_action[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s::det_state. P (scheduler_action s)\<rbrace>"
  assumes arch_post_modify_registers_ready_queues[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_post_modify_registers_cur'[wp]:
    "\<And>c f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_post_modify_registers c f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_post_modify_registers_not_idle_thread[wp]:
    "\<And>c t. \<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  assumes arch_post_cap_deletion_valid_sched[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_ct_not_in_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_simple_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_cur_thread[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_cur_thread t :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_sched_act_not[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>scheduler_act_not t :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_not_queued[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_queued t :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_post_cap_deletion_weak_valid_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>weak_valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_finalise_cap_idle_thread[wp] :
    "\<And>P b t. arch_finalise_cap t b \<lbrace>\<lambda> (s:: det_ext state). P (idle_thread s)\<rbrace>"
  assumes arch_invoke_irq_handler_valid_sched[wp]:
    "\<And>i. arch_invoke_irq_handler i \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes arch_mask_irq_signal_valid_sched[wp]:
    "\<And>irq. arch_mask_irq_signal irq \<lbrace>valid_sched :: det_state \<Rightarrow> _\<rbrace>"

context DetSchedSchedule_AI begin

crunch switch_to_idle_thread, switch_to_thread
  for valid_queues[wp]: "valid_queues :: det_state \<Rightarrow> _"
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action)

crunch
  switch_to_idle_thread, switch_to_thread
  for weak_valid_sched_action[wp]: "weak_valid_sched_action :: det_state \<Rightarrow> _"
  (simp: whenE_def)

end

lemma tcb_sched_action_dequeue_ct_not_in_q_2_ct_upd:
  "\<lbrace>valid_queues\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) thread\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (fastforce simp: etcb_at_def ct_not_in_q_def valid_queues_def tcb_sched_dequeue_def
                         not_queued_def
                   dest: ko_at_etcbD
                  split: option.split)
  done

lemma tcb_sched_action_dequeue_valid_sched_action_2_ct_upd:
  "\<lbrace>valid_sched_action and
       (\<lambda>s. is_activatable_2 thread (scheduler_action s) (kheap s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. valid_sched_action_2 (scheduler_action s) (etcbs_of s) (kheap s) thread (cur_domain s)\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (clarsimp simp: etcb_at_def valid_sched_action_def split: option.split)
  done

context DetSchedSchedule_AI begin

lemma etcbs_of_arch_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_arch_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def)
  apply (wp | wpc)+
  apply clarsimp
  by (fastforce simp: valid_sched_def valid_queues_def
                      valid_sched_action_def is_activatable_def
                      weak_valid_sched_action_def st_tcb_at_kh_if_split
                      st_tcb_def2 valid_blocked_def)

lemma tcb_sched_action_dequeue_not_queued[wp]:
  "\<lbrace>valid_queues\<rbrace> tcb_sched_action tcb_sched_dequeue t \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  unfolding tcb_sched_action_def tcb_sched_dequeue_def
  apply wpsimp
  apply (fastforce simp: valid_queues_def etcb_at_def not_queued_def
                  dest!: ko_at_etcbD)
  done

lemma switch_to_thread_ct_not_queued[wp]:
  "\<lbrace>valid_queues\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s::det_state. not_queued (cur_thread s) s\<rbrace>"
  unfolding switch_to_thread_def
  by wpsimp

end

lemma ct_not_in_q_def2:
  "ct_not_in_q_2 queues sa ct = (sa = resume_cur_thread \<longrightarrow> (\<forall>d p. ct \<notin> set (queues d p)))"
  by (fastforce simp add: ct_not_in_q_def not_queued_def)

context DetSchedSchedule_AI begin

lemma switch_to_thread_ct_not_in_q[wp]:
  "\<lbrace>valid_queues\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: ct_not_in_q_def2 not_queued_def[symmetric])
  apply (wp hoare_drop_imps | simp)+
  done

lemma switch_to_thread_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and is_activatable t\<rbrace>
     switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: tcb_sched_action_dequeue_valid_sched_action_2_ct_upd simp: switch_to_thread_def)

end

lemma tcb_sched_action_dequeue_ct_in_cur_domain':
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_ s. ct_in_cur_domain (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (simp add: etcb_at_def split: option.split)
  done

context DetSchedSchedule_AI begin

crunch as_user
  for ct_in_cur_domain_2[wp]: "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"
  (wp: set_object_wp)

lemma switch_to_thread_ct_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)\<rbrace>
   switch_to_thread thread
   \<lbrace>\<lambda>_. ct_in_cur_domain :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wpsimp wp: tcb_sched_action_dequeue_ct_in_cur_domain')
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
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_blocked_def split: option.splits)
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
  apply (simp add: as_user_def set_object_def get_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=tp in spec)
  apply (drule get_tcb_SomeD, simp)
  apply (simp add: ct_in_q_def)
  apply (case_tac "tp = cur_thread s"; clarsimp simp: st_tcb_at_def obj_at_def)
  done
end

crunch do_machine_op
  for ct_in_q[wp]: ct_in_q

lemma do_machine_op_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wpsimp | auto)+

context DetSchedSchedule_AI begin

lemma switch_to_thread_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp|wpc)+
     prefer 4
     apply (rule get_wp)
    prefer 3
    apply (rule assert_inv)
   prefer 2
   apply (rule arch_switch_to_thread_valid_blocked)
  by (wp tcb_sched_action_dequeue_ct_in_cur_domain' tcb_sched_action_dequeue_valid_blocked')

crunch switch_to_thread
  for etcb_at[wp]: "etcb_at P t :: det_state \<Rightarrow> _"

lemma switch_to_thread_valid_sched:
  "\<lbrace>is_activatable t and in_cur_domain t and valid_sched_action and valid_queues and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: valid_sched_def | wp | simp add: ct_in_cur_domain_2_def)+
  done

crunch switch_to_idle_thread
  for valid_idle[wp]: "valid_idle :: det_ext state \<Rightarrow> bool"

crunch switch_to_thread
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action (s :: det_ext state))"

end

crunch update_cdt_list
  for valid_queues[wp]: "valid_queues"
crunch update_cdt_list
  for ct_not_in_q[wp]: "ct_not_in_q"
crunch update_cdt_list
  for weak_valid_sched_action[wp]: "weak_valid_sched_action"
crunch update_cdt_list
  for valid_sched_action[wp]: "valid_sched_action"
crunch update_cdt_list
  for valid_blocked[wp]: valid_blocked
crunch update_cdt_list
  for valid_sched[wp]: "valid_sched"

crunch set_cdt, set_cap
  for valid_queues[wp]: valid_queues
  (wp: valid_queues_lift)
crunch set_cdt, set_cap
  for ct_not_in_q[wp]: ct_not_in_q
  (wp: ct_not_in_q_lift)
crunch set_cdt, set_cap
  for weak_valid_sched_action[wp]: weak_valid_sched_action
  (wp: weak_valid_sched_action_lift)
crunch set_cdt, set_cap
  for valid_sched_action[wp]: valid_sched_action
  (wp: valid_sched_action_lift)
crunch set_cdt, set_cap
  for valid_blocked[wp]: valid_blocked
  (wp: valid_blocked_lift)
crunch set_cdt, set_cap
  for valid_sched[wp]: valid_sched
  (wp: valid_sched_lift set_cap_typ_at)

crunch cap_insert
  for ct_not_in_q[wp]: "ct_not_in_q"
  (wp: hoare_drop_imps dxo_wp_weak)

crunch cap_insert
  for weak_valid_sched_action[wp]: "weak_valid_sched_action"
  (wp: hoare_drop_imps dxo_wp_weak)

lemma valid_queues_trivial[simp]: "valid_queues_2 (\<lambda>_ _. []) kh ekh"
by (simp add: valid_queues_def)

lemma ct_not_in_q_trivial[simp]: "ct_not_in_q_2 (\<lambda>_ _. []) sa ct"
  by (simp add: ct_not_in_q_def not_queued_def)

lemma st_tcb_at_get_lift: "get_tcb thread s = Some y \<Longrightarrow> test (tcb_state y) \<Longrightarrow>
         st_tcb_at test thread s"
  by (simp add: ct_in_state_def st_tcb_def2)

lemmas det_ext_simps[simp] = select_switch_det_ext_ext_def unwrap_ext_det_ext_ext_def


lemma guarded_switch_to_lift:
  "\<lbrace>P\<rbrace> switch_to_thread thread \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> guarded_switch_to thread \<lbrace>Q\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def get_thread_state_def thread_get_def)

lemma tcb_sched_action_lift:
  "(\<And>f s. P s \<Longrightarrow> P (ready_queues_update f s))
  \<Longrightarrow> \<lbrace>P\<rbrace> tcb_sched_action a b \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp | simp add: tcb_sched_action_def etcb_at_def)+

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
  "\<lbrace>\<top>\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. thread \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def
                  split: option.splits)
  done

lemma enqueue_nonempty:
  "\<lbrace>\<top>\<rbrace>
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

crunch switch_to_idle_thread
  for etcb_at[wp]: "etcb_at P t :: det_state \<Rightarrow> _"

lemma switch_to_idle_thread_valid_sched:
  "\<lbrace>valid_sched_action and valid_idle and valid_queues and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (simp add: valid_sched_def | wp)+

crunch choose_thread
  for etcb_at[wp]: "etcb_at P t :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma choose_thread_valid_sched[wp]:
  "\<lbrace>valid_sched_action and valid_idle and valid_queues and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
     choose_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: choose_thread_def)
  apply (wp guarded_switch_to_lift switch_to_idle_thread_valid_sched switch_to_thread_valid_sched)
  apply (clarsimp simp: valid_queues_def next_thread_def is_activatable_2_def
                 dest!: next_thread_queued)
  apply (fastforce simp: st_tcb_def2 in_cur_domain_def etcb_at_def split: option.splits)
  done

end

lemma tcb_sched_enqueue_in_cur_domain:
  "\<lbrace>in_cur_domain w\<rbrace> tcb_sched_action tcb_sched_enqueue t \<lbrace>\<lambda>_. in_cur_domain w\<rbrace>"
  apply (simp add: tcb_sched_action_def in_cur_domain_def | wp)+
  done

crunch next_domain
  for valid_queues: valid_queues
  and valid_blocked: valid_blocked
  and ct_in_q: ct_in_q
  and ct_not_in_q: ct_not_in_q
  (simp: Let_def ct_in_q_def wp: dxo_wp_weak)

lemma next_domain_valid_sched_action:
  "\<lbrace>\<lambda>s. scheduler_action s = choose_new_thread\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: next_domain_def thread_set_domain_def)
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: Let_def valid_sched_action_def weak_valid_sched_action_def)
  done

lemma tcb_sched_action_dequeue_in_cur_domain[wp]:
  "\<lbrace>in_cur_domain thread\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_. in_cur_domain thread\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (simp add: etcb_at_def split: option.split)
  done

context DetSchedSchedule_AI begin
lemma switch_to_thread_cur_in_cur_domain[wp]:
  "\<lbrace>in_cur_domain t\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_ s::det_state. in_cur_domain (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_thread_def | wp | wps)+
  done
end

lemma tcb_sched_enqueue_cur_ct_in_q:
  "\<lbrace>\<lambda>s. cur = cur_thread s\<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_enqueue_def split: option.splits)
  done

lemma tcb_sched_enqueue_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_enqueue_def split: option.splits)
  done

lemma tcb_sched_append_ct_in_q:
  "\<lbrace> ct_in_q \<rbrace> tcb_sched_action tcb_sched_append cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_append_def split: option.splits)
  done

context DetSchedSchedule_AI begin
crunch switch_to_idle_thread, next_domain
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)
end

lemma set_scheduler_action_rct_switch_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))\<rbrace>
   set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply clarsimp
  done

lemma set_scheduler_action_rct_switch_thread_valid_sched:
  "\<lbrace>valid_sched and ct_not_queued
          and (\<lambda>s. st_tcb_at activatable (cur_thread s) s)
          and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)
          and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))\<rbrace>
     set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp set_scheduler_action_rct_switch_thread_valid_blocked | force)+

context DetSchedSchedule_AI begin
lemma switch_to_thread_sched_act_is_cur:
  "\<lbrace>\<lambda>s. scheduler_action s = switch_thread word\<rbrace> switch_to_thread word
       \<lbrace>\<lambda>rv s. scheduler_action s = switch_thread (cur_thread s)\<rbrace>"
  by (simp add: switch_to_thread_def | wp)+
end

crunch next_domain
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  (simp: Let_def wp: dxo_wp_weak)

context DetSchedSchedule_AI begin

lemma choose_thread_ct_not_queued:
  "\<lbrace> valid_queues and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_ct_activatable:
  "\<lbrace> valid_queues and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_ s::det_state.  st_tcb_at activatable (cur_thread s) s \<rbrace>"
  apply (wpsimp simp: choose_thread_def
                wp: guarded_switch_to_lift stit_activatable'[simplified ct_in_state_def]
                    stt_activatable[simplified ct_in_state_def])
  apply (fastforce dest!: next_thread_queued
                   simp: next_thread_def valid_queues_def is_activatable_def in_cur_domain_def)
  done

lemma choose_thread_cur_dom_or_idle:
  "\<lbrace> valid_queues \<rbrace>
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
                   simp: etcb_at_def next_thread_def valid_queues_def in_cur_domain_def)
  done

crunch choose_thread
  for sched_act[wp]: "\<lambda>s::det_state. P (scheduler_action s)"
  (wp: guarded_switch_to_lift)

lemma valid_sched_action_from_choose_thread:
  "scheduler_action s = choose_new_thread \<Longrightarrow> valid_sched_action s"
  unfolding valid_sched_action_def by simp

crunch tcb_sched_action
  for sched_act[wp]: "in_cur_domain t"

crunch set_scheduler_action
  for ct_in_q[wp]: ct_in_q
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
  apply (erule_tac x=st in allE)
  apply (force simp: not_queued_def)
  done

lemma set_scheduler_action_cnt_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. scheduler_action s = switch_thread t \<and>
      (\<exists>d p. t \<in> set (ready_queues s d p)))\<rbrace>
   set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def wp: set_scheduler_action_cnt_valid_blocked'[where t=t])

lemma append_thread_queued:
  "\<lbrace>\<top>\<rbrace>
     tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. thread \<in> set (ready_queues s d prio))\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (fastforce simp: etcb_at_def tcb_sched_append_def
                  split: option.splits)
  done

(* having is_highest_prio match gets_wp makes it very hard to stop and drop imps etc. *)
definition
  "wrap_is_highest_prio cur_dom target_prio \<equiv> gets (is_highest_prio cur_dom target_prio)"

lemma schedule_choose_new_thread_valid_sched:
  "\<lbrace> valid_idle and valid_idle_etcb and valid_queues and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)
     and ct_in_q \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp_del: when_wp
                 wp: set_scheduler_action_rct_valid_sched choose_thread_ct_not_queued
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action
                      next_domain_valid_queues next_domain_valid_blocked next_domain_ct_in_q)+
  done

lemma schedule_valid_sched:
  "\<lbrace>valid_sched and valid_idle\<rbrace> schedule \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding schedule_def
  apply (wp, wpc)
         (* resume_cur_thread *)
         apply wp
        prefer 2
        (* choose new thread *)
        apply (wp schedule_choose_new_thread_valid_sched tcb_sched_action_enqueue_valid_blocked
                   tcb_sched_enqueue_cur_ct_in_q)
       (* switch_thread candidate *)
       apply (rename_tac candidate)
       apply (wp del: when_wp
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
           apply (wpsimp wp: thread_get_inv hoare_drop_imp)+ \<comment> \<open>FIXME: remove @{thm thread_get_prio_wp} from wp?\<close>
       apply (strengthen valid_blocked_valid_blocked_except)
       apply (wp tcb_sched_action_enqueue_valid_blocked tcb_sched_enqueue_cur_ct_in_q gts_wp )+

  apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                        switch_in_cur_domain_def)
  apply (safe ; (fastforce elim: st_tcb_at_opeqI
                 | fastforce simp: valid_sched_def valid_blocked_def valid_blocked_except_def
                                   valid_sched_action_def weak_valid_sched_action_def
                                   switch_in_cur_domain_def ct_in_q_def ct_not_in_q_def
                                   st_tcb_at_def obj_at_def)?)
  done

crunch as_user
  for ct_not_in_q[wp]: ct_not_in_q
  (wp: ct_not_in_q_lift)

crunch update_restart_pc
  for ct_not_in_q[wp]: "\<lambda>s. ct_not_in_q s"


crunch
  thread_set, cancel_all_ipc, unbind_maybe_notification, cancel_all_signals, unbind_notification,
  blocked_cancel_ipc, fast_finalise, deleted_irq_handler
  for ct_not_in_q[wp]: ct_not_in_q
  (wp: crunch_wps ignore: tcb_sched_action)

crunch finalise_cap
  for ct_not_in_q[wp]: "ct_not_in_q :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps ignore: tcb_sched_action)

end

lemma set_simple_ko_etcbs_of[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_wp_strong get_object_wp)
  by (auto elim!: rsubst[where P=P] simp: etcbs_of'_def obj_at_def)

lemma set_simple_ko_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (wp hoare_drop_imps valid_queues_lift | simp add: set_simple_ko_def)+

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
  "\<lbrace>valid_sched\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_lift | simp add: set_simple_ko_def)+

lemma cancel_all_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (wp mapM_x_wp' set_thread_state_runnable_valid_queues sts_st_tcb_at' hoare_drop_imps
          set_thread_state_runnable_weak_valid_sched_action hoare_vcg_all_lift
          set_thread_state_valid_blocked_except
          tcb_sched_action_enqueue_valid_blocked
          reschedule_required_valid_sched
     | wpc
     | rule subset_refl | simp)+
  apply (simp_all add: valid_sched_def valid_sched_action_def)
  done

lemma cancel_all_signals_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (wp mapM_x_wp' set_thread_state_runnable_valid_queues sts_st_tcb_at' hoare_drop_imps
          set_thread_state_runnable_weak_valid_sched_action hoare_vcg_all_lift
          set_thread_state_valid_blocked_except
          tcb_sched_action_enqueue_valid_blocked
          reschedule_required_valid_sched
       | wpc
       | rule subset_refl | simp)+
  apply (simp_all add: valid_sched_def valid_sched_action_def)
  done

lemma thread_set_etcbs:
  "\<lbrakk>\<And>x. tcb_priority (f x) = tcb_priority x; \<And>x. tcb_domain (f x) = tcb_domain x\<rbrakk> \<Longrightarrow>
  thread_set f tptr \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  by (auto elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp: etcbs_of'_def)

crunch thread_set
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma thread_set_valid_queues:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_priority (f x) = tcb_priority x;
    \<And>x. tcb_domain (f x) = tcb_domain x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_queues\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (rule valid_queues_lift; wpsimp wp: thread_set_no_change_tcb_state thread_set_etcbs)

lemma thread_set_weak_valid_sched_action:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift thread_set_no_change_tcb_state
        | simp add: thread_set_def)+

lemma thread_set_not_state_valid_sched:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x; \<And>x. tcb_priority (f x) = tcb_priority x;
    \<And>x. tcb_domain (f x) = tcb_domain x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_sched\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (rule valid_sched_lift; (wpsimp wp: thread_set_no_change_tcb_state thread_set_etcbs)?)

lemma unbind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_notification ntfnptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule bind_wp[OF _ gbn_sp])
  apply (case_tac ntfnptra, simp, wp, simp)
  apply (clarsimp)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (wp set_bound_notification_valid_sched, clarsimp)
  done

context DetSchedSchedule_AI begin

crunch cap_swap_for_delete, empty_slot, cap_delete_one
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
  (simp: unless_def)

lemma reply_cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (wp hoare_drop_imps thread_set_not_state_valid_sched | simp)+
  done

end

lemma st_tcb_at_not:
  "st_tcb_at (\<lambda>st. \<not> P st) t s = (\<not> st_tcb_at P t s \<and> tcb_at t s)"
  apply (clarsimp simp: not_pred_tcb)
  apply (fastforce simp: st_tcb_at_tcb_at)
  done

lemma set_thread_state_not_runnable_valid_queues:
  "\<lbrace>valid_queues and ct_not_in_q and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add: set_object_def get_object_def | wp)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split ct_not_in_q_def
                         st_tcb_at_not)
  done

lemma set_thread_state_not_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add: set_object_def get_object_def | wp gts_wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                        st_tcb_at_not)
  done

lemma set_thread_state_not_runnable_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_thread_state_not_runnable_weak_valid_sched_action)+
  done

lemma set_thread_state_not_runnable_valid_blocked:
  "\<lbrace>valid_blocked and K (\<not> runnable ts)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_thread_state_def set_thread_state_act_def)
  apply (simp add: set_object_def get_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wp gts_wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def st_tcb_at_def obj_at_def get_tcb_def)
  apply (case_tac ts, simp_all)
  done

lemma set_thread_state_not_runnable_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s) and K (\<not> runnable ts)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def |
         wp set_thread_state_not_runnable_valid_queues
                                        set_thread_state_not_runnable_valid_sched_action
                                        set_thread_state_not_runnable_valid_blocked)+
  done

lemma blocked_cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     blocked_cancel_ipc ts tptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp set_thread_state_not_runnable_valid_sched)
  apply simp
  done

lemma cancel_signal_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     cancel_signal tptr ntfnptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wp set_thread_state_not_runnable_valid_sched hoare_drop_imps | wpc | simp)+
  done

lemma (in DetSchedSchedule_AI) cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_ipc_def get_thread_state_def thread_get_def)
  apply (wp | wpc)+
  apply (fastforce intro: st_tcb_at_get_lift)
  done

(* valid_queues with thread not runnable *)
lemma tcb_sched_action_dequeue_strong_valid_sched:
  "\<lbrace>ct_not_in_q and valid_sched_action and ct_in_cur_domain and
    valid_blocked and st_tcb_at (\<lambda>st. \<not> runnable st) thread and
    (\<lambda>es. \<forall>d p. (\<forall>t\<in>set (ready_queues es d p). is_etcb_at' t (etcbs_of es) \<and>
        etcb_at (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) t es \<and>
        (t \<noteq> thread \<longrightarrow> st_tcb_at runnable t es)) \<and> distinct (ready_queues es d p)) and
    valid_idle_etcb\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (clarsimp simp: etcb_at_def valid_sched_def split: option.split)
  apply (rule conjI)
   apply (fastforce simp: etcb_at_def etcbs_of'_def is_etcb_at_def valid_queues_def2
                          tcb_sched_dequeue_def obj_at_def)
  apply (rule conjI)
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

lemma set_scheduler_action_simple_sched_action[wp]:
  "\<lbrace>K $ simple_sched_action_2 action\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (simp add: set_scheduler_action_def | wp)+

lemma reschedule_required_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> reschedule_required  \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (simp add: reschedule_required_def | wp)+

context DetSchedSchedule_AI begin

crunch update_restart_pc
  for simple_sched_action[wp]: "simple_sched_action"
  and valid_sched[wp]: "valid_sched"
  (simp: crunch_simps ignore: set_object)

crunch finalise_cap
  for simple_sched_action[wp]: "simple_sched_action :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps mapM_x_wp mapM_wp subset_refl
   simp: unless_def if_fun_split)

lemma suspend_valid_sched[wp]:
  notes bind_wp_fwd_inv = bind_wp_fwd[where P=I and Q'="\<lambda>_. I" for I]
  shows "\<lbrace>valid_sched and simple_sched_action\<rbrace> suspend t \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: suspend_def)
  apply (rule bind_wp_fwd_inv)
   apply wpsimp
  apply (rule bind_wp_fwd_inv)
   apply wp
  apply (rule bind_wp_fwd_inv)
   apply wpsimp
  apply (wp tcb_sched_action_dequeue_strong_valid_sched
       | simp)+
   apply (simp add: set_thread_state_def)
   apply (wp gts_wp | wpc |
          simp add: set_thread_state_def set_thread_state_act_def
                    reschedule_required_def set_scheduler_action_def
                    tcb_sched_action_def set_object_def get_object_def)+
  apply (simp only: st_tcb_at_kh_simp[symmetric])
  apply (clarsimp simp: valid_sched_def valid_queues_def st_tcb_at_kh_if_split
                        valid_sched_action_def simple_sched_action_def
                        is_activatable_def valid_blocked_def
                  split: scheduler_action.splits)+
  done

crunch finalise_cap
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

end

crunch cap_swap_for_delete, cap_insert
  for simple_sched_action[wp]: "simple_sched_action"
  (wp: dxo_wp_weak)

context DetSchedSchedule_AI begin

lemma rec_del_valid_sched'[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
    rec_del call
   \<lbrace>\<lambda>rv. valid_sched and simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wp preemption_point_inv' | simp)+
  done

lemma rec_del_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule rec_del_valid_sched')
  apply simp
  done

lemma rec_del_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

end

lemma tcb_dequeue_not_queued:
  "\<lbrace>valid_queues\<rbrace> tcb_sched_action tcb_sched_dequeue tptr \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  by (fastforce simp: etcb_at_def tcb_sched_dequeue_def not_queued_def valid_queues_def
               dest!: ko_at_etcbD
               split: option.splits)

crunch tcb_sched_action
  for ct_in_state[wp]: "ct_in_state P"
  (simp: ct_in_state_def pred_tcb_at_def obj_at_def)

lemma ct_in_state_def2: "ct_in_state test s = st_tcb_at test (cur_thread s) s"
   by (simp add: ct_in_state_def)

lemma set_mcpriority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mcpriority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

lemma set_nonmember_if_cong: "(a \<notin> set (if P then x else y)) = (if P then a \<notin> set x else a \<notin> set y)"
  by auto

lemma reschedule_preserves_valid_sched: "\<lbrace> valid_sched \<rbrace> reschedule_required \<lbrace> \<lambda>rv. valid_sched\<rbrace>"
  unfolding reschedule_required_def set_scheduler_action_def tcb_sched_action_def
  apply (rule hoare_pre)
  apply (wp|wpc)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: valid_sched_2_def ct_not_in_q_2_def valid_blocked_2_def)
  apply (rule conjI)
   defer
   apply (clarsimp simp: valid_sched_2_def ct_not_in_q_2_def valid_blocked_2_def)
  apply (clarsimp simp: valid_sched_2_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_queues_2_def valid_sched_action_2_def tcb_sched_enqueue_def
                         weak_valid_sched_action_2_def etcb_at_conj_is_etcb_at
                   dest!: ko_at_etcbD)
  apply (rule conjI)
   apply (clarsimp simp: ct_not_in_q_2_def)
  apply (clarsimp simp:  valid_blocked_2_def)
  apply (clarsimp simp:  not_queued_def)
  apply (erule_tac x=t in allE; simp)
  by (clarsimp simp:  set_nonmember_if_cong tcb_sched_enqueue_def split: if_split_asm; blast)

lemma set_scheduler_action_swt_weak_valid_sched_except:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  apply (force simp: valid_sched_def ct_not_in_q_def
                     valid_sched_action_def weak_valid_sched_action_def
                     in_cur_domain_def ct_in_cur_domain_def switch_in_cur_domain_def
                     valid_blocked_except_def simple_sched_action_def
                     valid_blocked_2_def is_activatable_2_def valid_idle_etcb_def
              split: scheduler_action.splits)
  done

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def weak_valid_sched_action_def
                        in_cur_domain_def ct_in_cur_domain_def switch_in_cur_domain_def valid_blocked_def
                        simple_sched_action_def
                 split: scheduler_action.splits)
  done

lemma set_sched_action_cnt_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (simp add: set_scheduler_action_def | wp)+
  apply (simp add: not_cur_thread_def)
  done

lemma reschedule_required_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: reschedule_required_def, wp)

lemma possible_switch_to_valid_sched_except:
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target and
    st_tcb_at runnable target and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: reschedule_required_valid_blocked_except
                    set_scheduler_action_swt_weak_valid_sched_except)+
  apply (clarsimp simp: etcb_at'_def not_cur_thread_2_def valid_sched_def valid_sched_action_def
                        in_cur_domain_def ct_in_cur_domain_2_def valid_blocked_def
                 dest!: ko_at_etcbD
                 split: option.splits)
  done

lemma thread_set_priority_valid_queues_not_q:
  "\<lbrace>valid_queues and not_queued t\<rbrace> thread_set_priority t p \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_queues_def is_etcb_at'_def etcb_at'_def etcbs_of'_def
                        not_queued_def
                 dest!: get_tcb_SomeD)
  by (fastforce simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)

crunch thread_set_priority
  for neq_st_tcb_at[wp]: "\<lambda>s. \<not> st_tcb_at P t s"
  and ct_not_in_q[wp]: ct_not_in_q
  (wp: set_object_wp thread_set_no_change_tcb_state_converse)

lemma thread_set_priority_valid_sched_action[wp]:
  "thread_set_priority p t \<lbrace>valid_sched_action\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: valid_sched_action_def weak_valid_sched_action_2_def
                         switch_in_cur_domain_def in_cur_domain_def
                         is_activatable_def st_tcb_at_kh_def obj_at_kh_def
                         etcb_at'_def etcbs_of'_def
                  dest!: get_tcb_SomeD)
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
  apply (clarsimp simp: valid_blocked_except_def st_tcb_at_kh_def obj_at_kh_def dest!:get_tcb_SomeD)
  done

lemma thread_set_priority_valid_blocked[wp]:
  "thread_set_priority p t \<lbrace>valid_blocked\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_def obj_at_kh_def dest!:get_tcb_SomeD)
  done

lemma thread_set_priority_weak_valid_sched_action[wp]:
  "thread_set_priority t p \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def
                        st_tcb_at_kh_def obj_at_kh_def
                 dest!: get_tcb_SomeD)
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
  "\<lbrace>valid_sched and not_queued t\<rbrace>thread_set_priority t p \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  by (wpsimp wp: thread_set_priority_valid_queues_not_q)

crunch thread_set_priority
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and st_tcb_at[wp]: "\<lambda>s. st_tcb_at P t s"
  (wp: thread_set_no_change_tcb_state)

lemma set_priority_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace> set_priority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding set_priority_def
   apply (wpsimp wp: gts_wp hoare_vcg_if_lift hoare_vcg_all_lift hoare_vcg_imp_lift'
                     tcb_dequeue_not_queued hoare_vcg_imp_lift hoare_vcg_disj_lift
                     tcb_sched_action_enqueue_valid_blocked
                     tcb_sched_action_dequeue_valid_blocked_except
                     tcb_sched_action_dequeue_valid_sched_not_runnable
                     reschedule_required_valid_sched_cur_thread
                     possible_switch_to_valid_sched_except
                     thread_set_priority_valid_queues_not_q
               simp: ct_in_state_def2[symmetric]
          | wps)+
  apply (auto simp: valid_sched_def valid_sched_action_def st_tcb_at_def obj_at_def not_cur_thread_def split: thread_state.splits)
  done

context DetSchedSchedule_AI begin

crunch
  set_mcpriority, cap_insert, cap_delete, option_update_thread
  for simple_sched_action[wp]: "simple_sched_action :: det_state \<Rightarrow> _"

crunch
  option_update_thread, set_mcpriority, finalise_cap, cap_swap_for_delete
  for idle_thread[wp]: "\<lambda>(s:: det_state). P (idle_thread s)"

crunch
  preemption_point
  for idle_thread[wp]: "\<lambda>(s:: det_state). P (idle_thread s)"
  (ignore: OR_choiceE
   simp: OR_choiceE_def wrap_ext_bool_det_ext_ext_def crunch_simps
   wp: crunch_wps
   ignore_del: preemption_point)

lemma rec_del_idle_thread[wp]:
  "\<lbrace>\<lambda>(s:: det_ext state). P (idle_thread s)\<rbrace> rec_del call \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  apply (rule rec_del_preservation)
      apply wp+
  done

crunch
  cap_delete
  for idle_thread[wp]: "\<lambda>(s:: det_state). P (idle_thread s)"

crunch cap_delete
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"

lemma tc_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action and (\<lambda>s. a \<noteq> idle_thread s)\<rbrace>
      invoke_tcb (ThreadControl a sl b mcp pr e f g)
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply clarsimp
  apply wp
        apply wpsimp
       apply wpc
        apply (clarsimp simp: if_apply_def2 eq_commute[where a=a] option_update_thread_def
               | wpsimp wp: hoare_drop_imps reschedule_preserves_valid_sched
                                  hoare_lift_Pf [where f= "cur_thread" and P="\<lambda>x s. x \<noteq> idle_thread s"]
                                  check_cap_inv cap_insert_valid_sched thread_set_not_state_valid_sched
                      cong: conj_cong imp_cong)+
  done

end

lemma possible_switch_to_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable target and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     possible_switch_to target \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding possible_switch_to_def
  apply (wpsimp wp: reschedule_required_valid_blocked set_scheduler_action_swt_weak_valid_sched
         | strengthen valid_blocked_valid_blocked_except)+
  by (fastforce simp: etcb_at'_def not_cur_thread_2_def valid_sched_def valid_sched_action_def
                      in_cur_domain_def ct_in_cur_domain_2_def valid_blocked_def
                      valid_blocked_except_def
                dest!: ko_at_etcbD
                split: option.splits)

lemma set_thread_state_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread thread\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv. not_cur_thread thread\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_def set_thread_state_act_def set_object_def get_object_def |
         wp gts_wp)+
  done

crunch setup_reply_master
  for valid_sched[wp]: valid_sched

crunch setup_reply_master
  for valid_queues[wp]: valid_queues

crunch setup_reply_master
  for ct_not_in_q[wp]: ct_not_in_q

crunch setup_reply_master
  for valid_sched_action[wp]: valid_sched_action

crunch setup_reply_master
  for ct_in_cur_domain[wp]: ct_in_cur_domain
  (wp: ct_in_cur_domain_lift)

crunch setup_reply_master
  for valid_blocked[wp]: valid_blocked

crunch
  thread_set, set_irq_state, deleted_irq_handler, set_cdt, set_bound_notification, setup_reply_master,
  blocked_cancel_ipc, cancel_signal, cancel_all_signals, cancel_all_ipc, unbind_maybe_notification
  for not_cur_thread[wp]: "not_cur_thread thread"
  (wp: crunch_wps)

context DetSchedSchedule_AI begin

crunch empty_slot, cancel_ipc
  for not_cur_thread[wp]: "not_cur_thread thread :: det_state \<Rightarrow> _"
  (wp: hoare_drop_imps mapM_x_wp simp: unless_def if_fun_split)

crunch setup_reply_master
  for etcb_at[wp]: "etcb_at P t"

lemma restart_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace> restart thread \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: restart_def | wp set_thread_state_runnable_valid_queues
                                    set_thread_state_runnable_valid_sched_action
                                    set_thread_state_valid_blocked_except
                                    sts_st_tcb_at' cancel_ipc_simple2
                                    possible_switch_to_valid_sched)+
    apply (rule_tac Q'="\<lambda>_. valid_sched and not_cur_thread thread and (\<lambda>s. thread \<noteq> idle_thread s)" in hoare_strengthen_post)
     apply wp
    apply (simp add: valid_sched_def)
   apply (simp add: if_fun_split)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: get_thread_state_def thread_get_def)
    apply wp
   apply (simp add: get_thread_state_def | wp hoare_drop_imps)+
  apply (clarsimp simp: not_cur_thread_def valid_sched_def valid_sched_action_def
                        is_activatable_def)
  apply (drule_tac test="\<lambda>ts. \<not> activatable ts" in st_tcb_at_get_lift)
   apply simp
  apply (simp only: st_tcb_at_not)
  apply simp
  done

end

lemma etcbs_of_arch_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_arch_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def)
  apply (wp | wpc)+
  apply clarsimp
  by (fastforce simp: valid_sched_def valid_queues_def
                      valid_sched_action_def is_activatable_def
                      weak_valid_sched_action_def st_tcb_at_kh_if_split
                      st_tcb_def2 valid_blocked_def)

crunch bind_notification
  for valid_sched[wp]: valid_sched

crunch suspend
  for it[wp]: "\<lambda> s. P (idle_thread s)"
(ignore: tcb_sched_action wp: dxo_wp_weak)

context DetSchedSchedule_AI begin
lemma invoke_tcb_valid_sched[wp]:
  "\<lbrace>invs and valid_sched and simple_sched_action and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (cases ti, simp_all only:)
        apply (wp mapM_x_wp | simp | rule subset_refl | rule reschedule_preserves_valid_sched |
               clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap |
               intro impI conjI)+
    apply (rename_tac option)
    apply (case_tac option)
     apply (wp mapM_x_wp | simp | rule subset_refl |
            clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap |
            rule reschedule_preserves_valid_sched | intro impI conjI)+
  done
end

lemma runnable_eq_active: "runnable = active"
  apply (rule ext)
  apply (case_tac st, simp_all)
  done

lemma handle_yield_valid_sched[wp]:
  "\<lbrace>valid_sched and ct_active\<rbrace> handle_yield \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: handle_yield_def | wp tcb_sched_action_append_valid_blocked tcb_sched_action_dequeue_valid_blocked_except reschedule_required_valid_sched)+
  apply (clarsimp simp: valid_sched_def ct_in_state_def valid_sched_action_def
                        runnable_eq_active)
  done

crunch store_word_offs
  for valid_sched[wp]: valid_sched

crunch set_mrs, as_user
  for exst[wp]: "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

crunch set_mrs,set_message_info
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp')

lemma set_mrs_etcbs[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_mrs_def store_word_offs_def
  supply if_split [split del]
  by (wpsimp simp: zipWithM_x_mapM wp: mapM_wp' set_object_wp)

crunch set_mrs
  for valid_sched[wp]: valid_sched
  (wp: valid_sched_lift)

lemmas gts_drop_imp = hoare_drop_imp[where f="get_thread_state p" for p]

lemma reschedule_required_switch_valid_blocked:
  "\<lbrace>\<lambda>s. case scheduler_action s of switch_thread t \<Rightarrow> valid_blocked_except t s | _ \<Rightarrow> False\<rbrace>
    reschedule_required \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: reschedule_required_def | wp set_scheduler_action_cnt_valid_blocked tcb_sched_action_enqueue_valid_blocked hoare_vcg_all_lift | wpc)+
    apply (simp add: tcb_sched_action_def)
    apply wp+
  apply (force simp: etcb_at_def tcb_sched_enqueue_def valid_blocked_def valid_blocked_except_def split: option.splits)
  done

lemma reschedule_required_switch_valid_sched:
  "\<lbrace>valid_queues and weak_valid_sched_action and (\<lambda>s. case scheduler_action s of switch_thread t \<Rightarrow> valid_blocked_except t s | _ \<Rightarrow> False) and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_switch_valid_blocked | force)+

lemma enqueue_thread_not_not_queued:
  "\<lbrace>\<lambda>s. t = thread \<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. \<not> not_queued t s \<rbrace>"
  apply (simp add: tcb_sched_action_def not_queued_def)
  apply wp
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def
                  split: option.splits)
  done

(* FIXME: Move *)
lemma valid_blocked_except_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>valid_blocked_except thread\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked_except thread\<rbrace>"
  apply (rule hoare_pre)
   apply (wps c e d)
   apply (simp add: valid_blocked_except_def)
   apply (wp hoare_weak_lift_imp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a)
   apply (rule hoare_convert_imp)
    apply (rule typ_at_st_tcb_at_lift)
     apply (wp a t)+
  apply (simp add: valid_blocked_except_def)
  done

crunch as_user
  for valid_blocked_except[wp]: "valid_blocked_except thread"
  (wp: valid_blocked_except_lift)


(* FIXME: Move *)
lemma set_simple_ko_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_simple_ko f ptr ntfn \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps valid_sched_action_lift | simp add: set_simple_ko_def)+

crunch cap_insert, set_extra_badge
  for not_cur_thread[wp]: "not_cur_thread t"
  (wp: hoare_drop_imps dxo_wp_weak)

lemma transfer_caps_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+


crunch as_user
  for not_cur_thread[wp]: "not_cur_thread t"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

crunch (in DetSchedSchedule_AI) do_ipc_transfer
  for not_cur_thread[wp]: "not_cur_thread t :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

lemmas set_thread_state_active_valid_sched_except_blocked =
  set_thread_state_runnable_valid_sched_except_blocked[simplified runnable_eq_active]

lemma set_thread_state_runnable_valid_blocked:
  "\<lbrace>valid_blocked and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (rule bind_wp[OF _ gets_the_get_tcb_sp])
  apply (rule_tac Q'="\<lambda>rv. valid_blocked and st_tcb_at runnable ref" in bind_wp_fwd)
   apply (wp set_object_wp)
   apply (clarsimp simp: valid_blocked_def not_queued_def runnable_eq_active
                         pred_tcb_at_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
  apply (simp add: set_thread_state_act_def)
  apply (rule bind_wp[OF _ gts_sp])
  apply (rule_tac S="runnable ts" in hoare_gen_asm_spec)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  by wpsimp

lemma set_thread_state_runnable_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp set_thread_state_runnable_valid_queues
                                        set_thread_state_runnable_valid_sched_action
                                        set_thread_state_runnable_valid_blocked)+
  done

context DetSchedSchedule_AI begin
lemma update_waiting_ntfn_valid_sched[wp]:
  "\<lbrace> \<lambda>s. valid_sched s \<and> hd queue \<noteq> idle_thread s \<and> (scheduler_action s = resume_cur_thread \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace>
   update_waiting_ntfn ntfnptr queue badge val
   \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (wp sts_st_tcb_at' possible_switch_to_valid_sched_except
            set_thread_state_runnable_valid_sched
            set_thread_state_runnable_valid_queues
            set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except
            | clarsimp)+
  apply (clarsimp simp add: valid_sched_def not_cur_thread_def ct_not_in_q_def)
  done

end

crunch dec_domain_time
  for valid_sched[wp]: valid_sched

lemma thread_set_valid_blocked_except:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   thread_set f tptr \<lbrace>valid_blocked_except t\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_blocked_except_lift thread_set_no_change_tcb_state)

lemma etcbs_of_update_tcb_time_slice[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
   etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_time_slice_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma timer_tick_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> timer_tick \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding timer_tick_def thread_set_time_slice_def
  apply (simp
         | wp gts_wp reschedule_required_valid_sched tcb_sched_action_append_valid_blocked
              thread_get_wp thread_set_not_state_valid_sched thread_set_valid_queues
              thread_set_no_change_tcb_state thread_set_weak_valid_sched_action
              thread_set_valid_blocked_except thread_set_etcbs
         | wpc
         | rule hoare_strengthen_post, rule dec_domain_time_valid_sched,
           simp add: valid_sched_def valid_sched_action_def)+
  by (fastforce simp: valid_sched_def valid_queues_def valid_sched_action_def obj_at_def pred_tcb_at_def)

lemma cancel_badged_sends_filterM_valid_queues[wp]:
   "\<lbrace>valid_queues\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp set_thread_state_runnable_valid_queues sts_st_tcb_at' | simp)+
  done

lemma cancel_badged_sends_filterM_weak_valid_sched_action[wp]:
   "\<lbrace>weak_valid_sched_action\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at' | simp)+
  done

lemma cancel_badged_sends_filterM_ct_in_cur_domain[wp]:
   "\<lbrace>ct_in_cur_domain\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
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

lemma cancel_badged_sends_filterM_valid_blocked[wp]:
   "\<lbrace>valid_blocked\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp tcb_sched_action_enqueue_valid_blocked set_thread_state_valid_blocked_except | simp)+
  done

lemma cancel_badged_sends_filterM_valid_idle_etcb[wp]:
  notes valid_idle_etcb_lift[wp del]
  shows
   "\<lbrace>valid_idle_etcb\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
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

lemma cancel_badged_sends_valid_sched[wp]:
  shows
  "\<lbrace>valid_sched\<rbrace> cancel_badged_sends epptr badge \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (wp hoare_drop_imps reschedule_required_valid_sched | wpc | simp)+
   apply (simp_all add: valid_sched_def valid_sched_action_def)
  done

context DetSchedSchedule_AI begin

lemma cap_revoke_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule validE_valid, rule cap_revoke_preservation)
    apply (wpsimp wp: preemption_point_inv')+
  done

lemma cap_revoke_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. simple_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  by (wp cap_revoke_preservation preemption_point_inv' | fastforce)+

end

lemma thread_set_state_eq_valid_queues:
  "\<lbrakk>\<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_queues and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wpsimp
  apply (clarsimp simp: valid_queues_def etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  apply (fastforce simp: st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_valid_sched_action:
  "\<lbrakk>\<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_sched_action and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wpsimp
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def is_activatable_def
                        etcbs_of_update_unrelated
                 dest!: get_tcb_SomeD)
  apply (fastforce simp: st_tcb_at_kh_if_split st_tcb_def2 dest!: get_tcb_SomeD)
  done

lemma thread_set_state_eq_ct_in_cur_domain:
  "\<lbrakk>\<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x\<rbrakk> \<Longrightarrow>
   \<lbrace>ct_in_cur_domain and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wpsimp
  apply (clarsimp simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)
  done

lemma thread_set_state_eq_valid_blocked:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_blocked and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (fastforce simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_def2)
  done

context DetSchedSchedule_AI begin
lemma thread_set_state_eq_valid_sched:
  "\<lbrakk>\<And>x. tcb_state (f x) = ts; \<And>x. etcb_of (f x) = etcb_of x\<rbrakk> \<Longrightarrow>
   \<lbrace>valid_sched and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wp thread_set_state_eq_valid_queues thread_set_state_eq_valid_blocked
            thread_set_state_eq_valid_sched_action thread_set_state_eq_ct_in_cur_domain
            thread_set_etcbs | simp)+
  done
end

crunch thread_set
  for exst[wp]: "\<lambda>s. P (exst s)"

lemma thread_set_not_idle_valid_idle:
  "\<lbrace>valid_idle and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
     thread_set f tptr \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def, wp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma thread_set_st_tcb_at:
  "(\<And>x. P (tcb_state (f x)))
  \<Longrightarrow> \<lbrace>\<top>\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. st_tcb_at P tptr\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def, wp)
  apply (clarsimp simp: valid_idle_def st_tcb_at_def obj_at_def)
  done

crunch cap_move
  for valid_sched[wp]: valid_sched
  (wp: dxo_wp_weak)

context DetSchedSchedule_AI begin
lemma invoke_cnode_valid_sched:
  "\<lbrace>valid_sched and invs and valid_cnode_inv a and simple_sched_action\<rbrace> invoke_cnode a \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply wpc
         apply (simp add: liftE_def | (wp hoare_vcg_all_lift)+ | wp (once) hoare_drop_imps | wpc)+
  apply force
  done
end

crunch set_extra_badge
  for valid_sched[wp]: valid_sched (wp: crunch_wps)

lemma transfer_caps_valid_sched:
  "\<lbrace>valid_sched\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+
  done

context DetSchedSchedule_AI begin

crunch do_ipc_transfer, handle_fault_reply
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
  (wp: crunch_wps)

lemma thread_set_ct_active_wp:
  "\<lbrace> ct_active \<rbrace> thread_set (tcb_fault_update u) t \<lbrace>\<lambda>rv. ct_active \<rbrace>"
  by (wp ct_in_state_thread_state_lift thread_set_no_change_tcb_state, simp)

lemma do_reply_transfer_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_objs and ct_active and cte_wp_at (is_reply_cap_to t') slot
       and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp set_thread_state_not_runnable_valid_sched sts_st_tcb_at'
            cap_delete_one_reply_st_tcb_at do_ipc_transfer_non_null_cte_wp_at2
            thread_set_not_state_valid_sched thread_set_no_change_tcb_state
            possible_switch_to_valid_sched_except
         | wpc | clarsimp split del: if_split)+
        apply (wp set_thread_state_runnable_valid_queues
                  set_thread_state_runnable_valid_sched_action
                  set_thread_state_valid_blocked_except sts_st_tcb_at')[1]
       apply (rule_tac Q'="\<lambda>_. valid_sched and not_cur_thread receiver
                               and (\<lambda>s. receiver \<noteq> idle_thread s)"
              in hoare_strengthen_post)
        apply wp
       apply (simp add: valid_sched_def)
      apply (wp possible_switch_to_valid_sched_except)+
           apply simp
           apply (rule conjI)
            apply clarsimp
            apply (rule_tac P="valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) receiver
                               and ct_active and (\<lambda>s. receiver \<noteq> idle_thread s)" in hoare_weaken_pre)
             apply (wp set_thread_state_runnable_valid_queues
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
  done

end

lemma set_thread_state_not_queued_valid_queues:
  "\<lbrace>valid_queues and not_queued thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add: set_thread_state_act_def set_object_def get_object_def)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split not_queued_def)
  done

lemma set_scheduler_action_cnt_is_activatable'[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>r s. is_activatable (t s) s\<rbrace>"
  apply (wp set_scheduler_action_wp)
  apply (simp add: is_activatable_def)
  done

lemma set_scheduler_action_cnt_switch_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  by (simp add: set_scheduler_action_def, wp, simp)

lemma set_thread_state_sched_act_not_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not thread\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def set_thread_state_def)
  apply (rule hoare_conjI)
   apply (wp gts_wp | simp add: set_thread_state_act_def set_object_def get_object_def)+
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                         scheduler_act_not_def is_activatable_def pred_tcb_at_def
                         obj_at_def)
  apply (wp gts_wp | simp add: set_thread_state_act_def set_object_def get_object_def)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                        scheduler_act_not_def is_activatable_def)
  done

lemma set_thread_state_sched_act_not_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not thread
      and not_queued thread and K (\<not> runnable ts)\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: valid_sched_def |
      wp set_thread_state_not_queued_valid_queues
                                    set_thread_state_not_runnable_valid_blocked
         set_thread_state_sched_act_not_valid_sched_action)+

lemma setup_caller_cap_sched_act_not_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not sender and not_queued sender\<rbrace>
     setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (auto simp: setup_caller_cap_def
     | wp set_thread_state_sched_act_not_valid_sched)+


(* strong in case of tcb_domain t = tcb_domain target *)
lemma possible_switch_to_sched_act_not[wp]:
  "\<lbrace>K(t \<noteq> target) and scheduler_act_not t\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def
              split del: if_split
        | wp | wpc)+
  apply (clarsimp simp: etcb_at_def scheduler_act_not_def split: option.splits)
  done


lemma possible_switch_to_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and K(target \<noteq> t)\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def split del: if_split | wp | wpc)+
  by (fastforce simp: etcb_at_def tcb_sched_enqueue_def simple_sched_action_def
                         not_queued_def scheduler_act_not_def
                   split: option.splits)

lemma set_thread_state_ready_queues[wp]:
  "\<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>
    set_thread_state thread ts
   \<lbrace>\<lambda>r s. P (ready_queues s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def[abs_def] reschedule_required_def
                   set_scheduler_action_def set_object_def get_object_def)
  apply (wp | wpc | simp add: tcb_sched_action_def)+
  done

crunch set_extra_badge
  for scheduler_act[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

crunch set_simple_ko, set_extra_badge, setup_caller_cap
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps)

context DetSchedSchedule_AI begin

crunch do_ipc_transfer
  for scheduler_act[wp]: "\<lambda>s :: det_state. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s :: det_state. P (ready_queues s)"
  (wp: crunch_wps ignore: const_on_failure rule: transfer_caps_loop_pres)

end

crunch set_thread_state_act
  for sched_act_not[wp]: "scheduler_act_not t"
  (ignore: set_scheduler_action
   simp: set_scheduler_action_def if_fun_split scheduler_act_not_def
   wp: gts_wp)

crunch set_thread_state, set_simple_ko
  for sched_act_not[wp]: "scheduler_act_not t"
  (wp: hoare_drop_imps)

context DetSchedSchedule_AI begin
lemma send_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and scheduler_act_not thread and not_queued thread
      and (ct_active or ct_idle) and invs\<rbrace>
   send_ipc block call badge can_grant can_grant_reply thread epptr \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (wp set_thread_state_sched_act_not_valid_sched | wpc)+
            apply ((wp set_thread_state_sched_act_not_valid_sched
                       setup_caller_cap_sched_act_not_valid_sched
                       possible_switch_to_valid_sched_except
                       hoare_vcg_if_lift2 hoare_drop_imps | simp)+)[5]
       apply (wp set_thread_state_runnable_valid_queues
                 set_thread_state_runnable_valid_sched_action
                 set_thread_state_valid_blocked_except sts_st_tcb_at')
      apply (clarsimp simp: conj.commute eq_commute)
      apply (rename_tac recvr q recv_state)
      apply (rule_tac Q'="\<lambda>_. valid_sched and scheduler_act_not thread and not_queued thread
                              and (\<lambda>s. recvr \<noteq> cur_thread s)
                              and (\<lambda>s. recvr \<noteq> idle_thread s \<and> recvr \<noteq> thread)"
               in hoare_strengthen_post)
       apply ((wp thread_set_ct_active_wp|wpc)+)[1]
      apply (clarsimp simp: valid_sched_def)
      apply (clarsimp simp: ct_in_state_def cte_wp_at_caps_of_state not_cur_thread_def)
     apply (simp | wp gts_wp hoare_vcg_all_lift)+
   apply (rename_tac recvr q recv_state)
    apply (wp hoare_vcg_imp_lift)
     apply ((simp add: set_simple_ko_def set_object_def | wp hoare_drop_imps | wpc)+)[1]
    apply (wpsimp wp: hoare_vcg_imp_lift get_object_wp
          | simp add: get_simple_ko_def
          | wpc |
           wp (once) hoare_vcg_all_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])
  apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def2 obj_at_def a_type_def
                        valid_sched_def valid_sched_action_def
                        weak_valid_sched_action_def scheduler_act_not_def
                  split: kernel_object.splits)+
    apply (rename_tac tcb recvr q rtcb ep recv_pl)
    apply (case_tac "recvr = idle_thread s")
     subgoal by (fastforce dest: invs_valid_idle simp: valid_idle_def pred_tcb_at_def obj_at_def)
    apply (case_tac "recvr = cur_thread s")
     subgoal by (fastforce simp: ct_in_state_def st_tcb_at_def2 obj_at_def)
    apply (clarsimp simp: is_activatable_def)
  done
end

lemma thread_set_tcb_fault_set_invs:
  "valid_fault f \<Longrightarrow> \<lbrace>invs\<rbrace>
     thread_set (tcb_fault_update (\<lambda>_. Some f)) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule thread_set_invs_trivial)
      apply (clarsimp simp: ran_tcb_cap_cases)+
  done

context DetSchedSchedule_AI begin
lemma send_fault_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched and st_tcb_at active tptr and scheduler_act_not tptr and
       not_queued tptr and (ct_active or ct_idle) and invs and (\<lambda>_. valid_fault fault)\<rbrace>
     send_fault_ipc tptr fault
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_fault_ipc_def Let_def)
  apply (wp send_ipc_valid_sched thread_set_not_state_valid_sched thread_set_no_change_tcb_state
            hoare_gen_asm'[OF thread_set_tcb_fault_set_invs]  hoare_drop_imps hoare_vcg_all_liftE_R
            ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            hoare_vcg_disj_lift
         | wpc | simp | wps)+
  done

crunch delete_caller_cap
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"

end

lemma handle_double_fault_valid_queues:
  "\<lbrace>valid_queues and not_queued tptr\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: handle_double_fault_def set_thread_state_def)
  apply (wp | simp add: set_thread_state_act_def set_object_def get_object_def)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split not_queued_def)
  done

lemma handle_double_fault_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tptr\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: handle_double_fault_def set_thread_state_def)
  apply (wp gts_wp | simp add: set_thread_state_act_def set_object_def get_object_def)+
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def
                        is_activatable_def pred_tcb_at_def obj_at_def
                        st_tcb_at_kh_if_split scheduler_act_not_def
                  split: scheduler_action.splits)
  done

lemma handle_double_fault_valid_sched:
  "\<lbrace>valid_sched and not_queued tptr and scheduler_act_not tptr\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  including no_pre
  apply (wpsimp wp: handle_double_fault_valid_queues handle_double_fault_valid_sched_action
                    set_thread_state_not_runnable_valid_blocked
              comb: hoare_weaken_pre
         | rule hoare_conjI | simp add: handle_double_fault_def | fastforce simp: simple_sched_action_def)+
  done

lemma send_fault_ipc_error_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_liftE_R)+ | wpc)+

lemma send_fault_ipc_error_cur_thread[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_liftE_R)+ | wpc)+

lemma send_fault_ipc_error_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_liftE_R)+ | wpc)+

context DetSchedSchedule_AI begin
lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and not_queued thread and (ct_active or ct_idle)
      and scheduler_act_not thread and invs and (\<lambda>_. valid_fault ex)\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_fault_def
  by (simp add: handle_fault_def |
      wp handle_double_fault_valid_sched send_fault_ipc_valid_sched)+
end

lemma idle_not_queued'':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s); queue \<times> {rt} \<subseteq> state_refs_of s ptr\<rbrakk> \<Longrightarrow>
     idle_thread s \<notin> queue"
  by (frule idle_no_refs, fastforce simp: valid_idle_def sym_refs_def)

context DetSchedSchedule_AI begin

lemma send_signal_valid_sched[wp]:
  "\<lbrace> valid_sched and invs \<rbrace> send_signal ntfnptr badge \<lbrace> \<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_signal_def)
  apply (wp get_simple_ko_wp possible_switch_to_valid_sched_except
            set_thread_state_runnable_valid_queues set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except sts_st_tcb_at' gts_wp  | wpc | clarsimp)+
       apply (rename_tac ntfn a st)
       apply (rule_tac Q'="\<lambda>rv s. valid_sched s \<and> a \<noteq> idle_thread s \<and> not_cur_thread a s" in hoare_strengthen_post)
        apply (wp gts_wp get_simple_ko_wp | simp add: valid_sched_def)+
  apply (clarsimp)
  apply (rule conjI, clarsimp, rule conjI)
    apply (frule invs_valid_idle)
    apply (clarsimp simp: receive_blocked_def split: thread_state.splits)
    apply (drule (1) st_tcb_at_idle_thread, clarsimp)
   apply (clarsimp simp: receive_blocked_def split: thread_state.splits)
   apply ((auto simp: pred_tcb_at_def obj_at_def valid_sched_action_def
            is_activatable_def not_cur_thread_def | drule sym)+)[1]
  apply (clarsimp)
  apply (frule invs_valid_idle)
  apply (drule_tac ptr=ntfnptr and rt=NTFNSignal and queue="set x" in idle_not_queued'')
    apply (clarsimp simp: invs_sym_refs)
   apply (simp add: state_refs_of_def obj_at_def)
  apply (frule invs_valid_objs)
  apply (simp add: valid_objs_def obj_at_def)
  apply (drule_tac x = ntfnptr in bspec)
   apply (simp add: dom_def)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (drule hd_in_set)
  apply (rule conjI, clarsimp)
  apply (clarsimp)
  apply (cut_tac t="hd x" and P="\<lambda>st. \<not>activatable st" in ntfn_queued_st_tcb_at)
       apply ((simp add: obj_at_def ntfn_q_refs_of_def invs_def valid_state_def valid_pspace_def)+)[4]
   apply simp
  apply (clarsimp simp add: valid_sched_def valid_sched_action_def is_activatable_def st_tcb_def2)
  done

crunch complete_signal
  for valid_sched[wp]: valid_sched
  (ignore: resetTimer ackInterrupt wp: gts_wp hoare_drop_imps
   simp: op_equal pred_tcb_weakenE hoare_if_r_and)

lemma receive_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and ct_active
          and not_queued thread and scheduler_act_not thread and invs\<rbrace>
   receive_ipc thread cap is_blocking
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  supply option.case_cong_weak[cong]
  apply (simp add: receive_ipc_def)
  apply (wp | wpc | simp)+
          apply (wp set_thread_state_sched_act_not_valid_sched | wpc)+
         apply ((wp set_thread_state_sched_act_not_valid_sched
                    setup_caller_cap_sched_act_not_valid_sched
                 | simp add: do_nbrecv_failed_transfer_def)+)[2]
                apply ((wp possible_switch_to_valid_sched_except sts_st_tcb_at' hoare_drop_imps
                           set_thread_state_runnable_valid_queues
                           set_thread_state_runnable_valid_sched_action
                           set_thread_state_valid_blocked_except | simp | wpc)+)[3]
              apply (rule_tac Q'="\<lambda>_. valid_sched and scheduler_act_not (sender) and not_queued (sender)
                                     and not_cur_thread (sender) and (\<lambda>s. sender \<noteq> idle_thread s)"
                           in hoare_strengthen_post)
               apply wp
              apply (simp add: valid_sched_def)
             apply ((wp | wpc)+)[1]
            apply (simp | wp gts_wp hoare_vcg_all_lift)+
           apply (wp hoare_vcg_imp_lift)
            apply ((simp add: set_simple_ko_def set_object_def
                    | wp hoare_drop_imps | wpc)+)[1]
           apply (wp hoare_vcg_imp_lift get_object_wp
                     set_thread_state_sched_act_not_valid_sched gbn_wp
                  | simp add: get_simple_ko_def do_nbrecv_failed_transfer_def a_type_def
                       split: kernel_object.splits
                  | wpc
                  | wp (once) hoare_vcg_all_lift hoare_vcg_ex_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])+
  apply (clarsimp simp: st_tcb_at_kh_if_split default_notification_def default_ntfn_def isActive_def)
  apply (rename_tac ref b R ntfn xh xi xj)
  apply (drule_tac t="hd xh" and P'="\<lambda>ts. \<not> active ts" in st_tcb_weakenE)
   apply clarsimp
  apply (simp only: st_tcb_at_not)
  apply (subgoal_tac "hd xh \<noteq> idle_thread s")
   apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def valid_queues_def st_tcb_at_not ct_in_state_def not_cur_thread_def runnable_eq_active not_queued_def scheduler_act_not_def split: scheduler_action.splits)
  (* clag from send_signal_valid_sched *)
  apply clarsimp
  apply (frule invs_valid_idle)
  apply (drule_tac ptr=ref in idle_not_queued)
    apply (clarsimp simp: invs_sym_refs)
   apply (simp add: state_refs_of_def obj_at_def)
  apply (frule invs_valid_objs)
  apply (simp add: valid_objs_def obj_at_def)
  apply (drule_tac x = ref in bspec)
   apply (simp add: dom_def)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (drule hd_in_set)
  apply simp
  done

end

crunch receive_signal
  for valid_sched: valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched)

crunch delete_caller_cap
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

context DetSchedSchedule_AI begin

crunch delete_caller_cap
  for sched_act_not[wp]: "scheduler_act_not t :: det_state \<Rightarrow> _"
  (simp: unless_def
   wp: hoare_drop_imps set_scheduler_action_wp mapM_x_wp
   ignore: set_scheduler_action)

end

lemma tcb_sched_action_enqueue_not_queued:
  "\<lbrace>not_queued t and K (thread \<noteq> t)\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def
                  split: option.splits)
  done

lemma reschedule_required_not_queued:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  apply (simp add: reschedule_required_def tcb_sched_action_def
                   set_scheduler_action_def | wp | wpc)+
  apply (clarsimp simp: etcb_at_def tcb_sched_enqueue_def not_queued_def
                        scheduler_act_not_def
                  split: option.splits)
  done

context DetSchedSchedule_AI begin
lemma cancel_all_ipc_not_queued:
  "\<lbrace>st_tcb_at active t and valid_objs and not_queued t and scheduler_act_not t
        and sym_refs \<circ> state_refs_of\<rbrace>
     cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. not_queued t :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (wp reschedule_required_not_queued | wpc | simp)+
      apply (rule hoare_gen_asm)
      apply (rule_tac S="set queue - {t}" in mapM_x_wp)
       apply (wp tcb_sched_action_enqueue_not_queued | clarsimp)+
      apply (erule notE, assumption)
     apply (wp reschedule_required_not_queued | simp add: get_ep_queue_def)+
     apply (rule hoare_gen_asm)
     apply (rule_tac S="set queue - {t}" in mapM_x_wp)
      apply (wp tcb_sched_action_enqueue_not_queued | clarsimp)+
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
end

crunch set_simple_ko
  for not_queued[wp]: "not_queued t"
  (wp: hoare_drop_imps)

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

lemma unbind_maybe_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_maybe_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  unfolding unbind_maybe_notification_def
  apply (wp thread_set_valid_objs_triv set_simple_ko_valid_objs hoare_drop_imp
            get_simple_ko_wp | wpc | simp add: tcb_cap_cases_def
         | strengthen unbind_notification_valid_objs_helper)+
   apply (clarsimp)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp:valid_obj_def valid_tcb_def)+
  done

lemma unbind_maybe_notification_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
     unbind_maybe_notification a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_maybe_notification_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  apply (rule conjI)
   apply clarsimp
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_split_asm)
    apply (frule ko_at_state_refs_ofD, simp)
   apply (clarsimp split: if_split_asm)
   apply (frule ko_at_state_refs_ofD, simp)
   apply (fastforce simp: symreftype_inverse' dest!: refs_in_ntfn_q_refs)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm, frule ko_at_state_refs_ofD, simp)+
   apply (frule_tac P="(=) (Some a)" in ntfn_bound_tcb_at, simp_all add: obj_at_def)[1]
   apply (fastforce simp: ntfn_q_refs_no_NTFNBound obj_at_def is_tcb state_refs_of_def
                          tcb_st_refs_of_no_NTFNBound tcb_bound_refs_def2 tcb_ntfn_is_bound_def
                          tcb_st_refs_no_TCBBound
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (frule ko_at_state_refs_ofD, simp)
  done

crunch unbind_maybe_notification, unbind_notification
  for not_queued[wp]: "not_queued t"

context DetSchedSchedule_AI begin

lemma fast_finalise_not_queued:
  "\<lbrace>not_queued t and (st_tcb_at active t and valid_objs and scheduler_act_not t and
    sym_refs \<circ> state_refs_of)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. not_queued t :: det_state \<Rightarrow> _\<rbrace>"
  apply (cases cap, simp_all)
     apply (wp cancel_all_ipc_not_queued cancel_all_signals_not_queued
            get_simple_ko_wp unbind_maybe_notification_valid_objs | simp)+
  done

crunch delete_caller_cap
  for not_queued: "not_queued t :: det_state \<Rightarrow> _"
  (wp: fast_finalise_not_queued hoare_drop_imps simp: if_fun_split unless_def)

end

lemma set_simple_ko_ct_active:
  "\<lbrace>ct_active\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def | wp get_object_wp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
                  split: kernel_object.splits)
  done

crunch setup_reply_master
  for weak_valid_sched_action[wp]: "weak_valid_sched_action"

lemma cap_insert_check_cap_ext_valid[wp]:"
  \<lbrace>valid_list\<rbrace>
   check_cap_at new_cap src_slot (check_cap_at t slot (cap_insert new_cap src_slot x))
  \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (wp get_cap_wp | simp)+
  done

lemma opt_update_thread_valid_sched[wp]:
  "\<lbrakk>\<And>x a. tcb_state (fn a x) = tcb_state x; \<And>x a. etcb_of (fn a x) = etcb_of x\<rbrakk> \<Longrightarrow>
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

crunch delete_caller_cap
  for ct_active[wp]: ct_active (wp: ct_in_state_thread_state_lift)

context DetSchedSchedule_AI begin

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active
      and ct_not_queued and scheduler_act_sane\<rbrace>
   handle_recv is_blocking \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
              cong: if_cong)
  apply (wp get_simple_ko_wp handle_fault_valid_sched delete_caller_cap_not_queued
            receive_ipc_valid_sched receive_signal_valid_sched | simp)+
     apply (rule hoare_vcg_conj_elimE)
      apply (wpsimp simp: lookup_cap_def lookup_slot_for_thread_def)
       apply (wp resolve_address_bits_valid_fault2)+
    apply (simp add: valid_fault_def)
    apply (wp hoare_drop_imps hoare_vcg_all_liftE_R)
   apply (wpsimp wp: delete_caller_cap_not_queued | strengthen invs_valid_tcb_ctable_strengthen)+
  apply (auto simp: ct_in_state_def tcb_at_invs objs_valid_tcb_ctable invs_valid_objs)
  done

lemma handle_recv_valid_sched':
  "\<lbrace>invs and valid_sched and ct_active and ct_not_queued and scheduler_act_sane\<rbrace>
    handle_recv is_blocking
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (wp handle_recv_valid_sched)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  done

end

crunch reply_from_kernel
  for valid_sched[wp]: valid_sched

lemma set_thread_state_active_valid_sched:
  "active st \<Longrightarrow>
   \<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct)\<rbrace>
     set_thread_state ct st \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_queues_def)
  apply (wp hoare_vcg_all_lift)
    apply (rule hoare_lift_Pf [where f="\<lambda>s. ready_queues s", OF _ set_thread_state_ready_queues])
    apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_cases simp: runnable_eq_active)
   apply (wp set_thread_state_runnable_valid_sched_action set_thread_state_runnable_valid_blocked)
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def runnable_eq_active)
  done

lemma set_thread_state_Running_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct)\<rbrace>
     set_thread_state ct Running \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule set_thread_state_active_valid_sched) simp

lemma set_thread_state_Restart_valid_sched:
  "\<lbrace>valid_sched and ct_active and (\<lambda>s. cur_thread s = ct)\<rbrace>
     set_thread_state ct Restart \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (rule set_thread_state_active_valid_sched) simp

context DetSchedSchedule_AI begin
crunch invoke_irq_control, invoke_irq_handler
  for valid_sched[wp]: "valid_sched :: det_state \<Rightarrow> _"
end

lemma simple_sched_action_sched_act_not[simp]:
  "simple_sched_action s \<Longrightarrow> scheduler_act_not t s"
  by (fastforce simp: simple_sched_action_def scheduler_act_not_def)

declare valid_idle_etcb_lift[wp del]

crunch thread_set_domain
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  and sched[wp]: "\<lambda>s. P (scheduler_action s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"

lemma thread_set_domain_st_tcb[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (st_tcb_at Q p s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_not_idle_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb and valid_idle and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
   thread_set_domain tptr d
   \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_idle_etcb_def etcb_at'_def etcbs_of'_def valid_idle_def
                        pred_tcb_at_def obj_at_def)
  done

lemma thread_set_domain_cur_activatable[wp]:
  "thread_set_domain tptr d \<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>"
  unfolding is_activatable_def
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: hoare_vcg_imp_lift)

lemma thread_set_domain_weak_valid_sched_action[wp]:
  "thread_set_domain tptr d \<lbrace>weak_valid_sched_action\<rbrace>"
  unfolding weak_valid_sched_action_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma thread_set_domain_not_switch_switch_in_cur_domain:
  "\<lbrace>switch_in_cur_domain and (\<lambda>s. scheduler_action s \<noteq> switch_thread tptr)\<rbrace>
   thread_set_domain tptr d
   \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def is_etcb_at_def etcb_at_def etcbs_of'_def
                 dest!:get_tcb_SomeD)
  done

lemma thread_set_domain_ssa_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
   thread_set_domain tptr d
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_not_switch_switch_in_cur_domain)
  apply (force simp: simple_sched_action_def)
  done

lemma thread_set_domain_valid_blocked[wp]:
  "thread_set_domain tptr d \<lbrace>valid_blocked\<rbrace>"
  by (wpsimp wp: valid_blocked_lift)

lemma thread_set_domain_valid_blocked_except[wp]:
  "thread_set_domain tptr d \<lbrace>valid_blocked_except t\<rbrace>"
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

lemma thread_set_domain_valid_queues_not_q:
  "\<lbrace>valid_queues and not_queued t\<rbrace> thread_set_domain t d \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_queues_def is_etcb_at'_def etcb_at'_def etcbs_of'_def
                        not_queued_def
                 dest!: get_tcb_SomeD)
  by (fastforce simp: st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)

lemma thread_set_domain_ct_not_in_q[wp]:
  "thread_set_domain p d \<lbrace>ct_not_in_q\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp wp: set_object_wp)

lemma thread_set_domain_not_idle_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and not_queued tptr and (\<lambda>s. tptr \<noteq> cur_thread s) and (\<lambda>s. tptr \<noteq> idle_thread s) and valid_idle\<rbrace>
   thread_set_domain tptr d
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding valid_sched_def valid_sched_action_def
  apply (wpsimp wp: thread_set_domain_valid_queues_not_q thread_set_domain_ct_in_cur_domain
                    thread_set_domain_not_switch_switch_in_cur_domain
                    thread_set_domain_not_idle_valid_idle_etcb)
  apply (clarsimp simp: simple_sched_action_def not_cur_thread_def)
  done

declare tcb_sched_action_valid_idle_etcb[wp]

lemma invoke_domain_valid_sched[wp]:
  "\<lbrace>valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s)
                and simple_sched_action and valid_idle\<rbrace>
    invoke_domain t d \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: invoke_domain_def)
  apply wp
   apply (simp add: set_domain_def)
   apply (wp gts_st_tcb_at hoare_vcg_if_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift
             hoare_vcg_disj_lift reschedule_required_valid_sched
             tcb_sched_action_enqueue_valid_blocked
             thread_set_domain_valid_queues_not_q
             thread_set_domain_ssa_valid_sched_action
             thread_set_domain_ct_in_cur_domain thread_set_domain_not_idle_valid_sched
             thread_set_domain_not_idle_valid_idle_etcb)
      apply (wp tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except)
     apply simp
     apply (wp hoare_vcg_disj_lift)
     apply (rule_tac Q'="\<lambda>_. valid_sched and not_queued t and valid_idle and (\<lambda>s. t \<noteq> idle_thread s)" in hoare_strengthen_post)
      apply (wp tcb_sched_action_dequeue_valid_sched_not_runnable tcb_dequeue_not_queued)
     apply (simp add: valid_sched_def valid_sched_action_def)
    apply simp
    apply (wp hoare_vcg_disj_lift tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except
              tcb_sched_action_dequeue_valid_sched_not_runnable)+
  apply (clarsimp simp: valid_sched_def not_cur_thread_def valid_sched_action_def not_pred_tcb)
  apply (auto simp: st_tcb_def2 tcb_at_def)
  done


lemma idle_not_reply_cap:
  "\<lbrakk> valid_idle s; valid_reply_caps s; cte_wp_at (is_reply_cap_to r) p s \<rbrakk> \<Longrightarrow> r \<noteq> idle_thread s"
  apply (drule_tac p=p in valid_reply_caps_of_stateD',assumption)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma idle_not_reply_cap':
  "\<lbrakk> valid_idle s; valid_reply_caps s; cte_wp_at ((=) (ReplyCap r False R)) p s \<rbrakk>
   \<Longrightarrow> r \<noteq> idle_thread s"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule_tac p=p in valid_reply_caps_of_stateD,assumption)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

context DetSchedSchedule_AI begin
lemma perform_invocation_valid_sched[wp]:
  "\<lbrace>invs and valid_invocation i and ct_active and simple_sched_action and valid_sched
         and (\<lambda>s. not_queued (cur_thread s) s)\<rbrace>
     perform_invocation calling blocking i
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (cases i, simp_all)
          apply (wp invoke_untyped_valid_sched send_ipc_valid_sched | clarsimp)+
         apply (clarsimp simp: ct_in_state_def)
        apply (wp invoke_cnode_valid_sched send_ipc_valid_sched invoke_domain_valid_sched
             | simp add: invs_valid_objs idle_not_reply_cap invs_valid_idle invs_valid_reply_caps
                         is_reply_cap_to_def
             | clarsimp simp: ct_in_state_def)+
  done
end

crunch set_thread_state_act
  for not_queued[wp]: "not_queued t"

crunch set_thread_state
  for ct_not_queued[wp]: ct_not_queued (wp: ct_not_queued_lift)

context DetSchedSchedule_AI begin
lemma handle_invocation_valid_sched:
  "\<lbrace>invs and valid_sched and ct_active and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     handle_invocation a b
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid handle_fault_valid_sched | wpc)+
                apply (wp set_thread_state_runnable_valid_sched)[1]
               apply wp+
         apply (wp gts_wp hoare_vcg_all_lift)
        apply (rule_tac Q'="\<lambda>_. valid_sched" and E'="\<lambda>_. valid_sched" in hoare_strengthen_postE)
          apply wp
         apply ((clarsimp simp: st_tcb_at_def obj_at_def)+)[2]
       apply (wp ct_in_state_set set_thread_state_runnable_valid_sched
             | simp add: split_def if_apply_def2 split del: if_split)+
      apply (simp add: validE_E_def)
      apply (rule hoare_strengthen_postE)
        apply (rule lookup_cap_and_slot_valid_fault)
       apply (wp | simp)+
  apply (auto simp: ct_in_state_def valid_sched_def ct_not_in_q_def valid_queues_def not_queued_def runnable_eq_active elim: st_tcb_ex_cap)
  done
end

lemma valid_sched_ct_not_queued:
  "\<lbrakk>valid_sched s; scheduler_action s = resume_cur_thread\<rbrakk> \<Longrightarrow>
    not_queued (cur_thread s) s"
  by (fastforce simp: valid_sched_def ct_not_in_q_def)

context DetSchedSchedule_AI begin
lemma handle_reply_valid_sched:
  "\<lbrace>valid_sched and ct_active and invs\<rbrace> handle_reply \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_reply_def)
  apply (wp get_cap_wp | wpc | clarsimp)+

  apply (auto simp: invs_valid_objs idle_not_reply_cap' invs_valid_idle invs_valid_reply_caps is_reply_cap_to_def | erule cte_wp_at_lift)+

done
end

crunch do_machine_op, cap_insert, set_extra_badge
  for ct_not_queued[wp]: "\<lambda>s. not_queued (cur_thread s) s"
  (wp: hoare_drop_imps dxo_wp_weak)

lemma transfer_caps_ct_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
     transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

crunch set_thread_state
  for ct_sched_act_not[wp]: "\<lambda>s. scheduler_act_not (cur_thread s) s"
  (wp: set_scheduler_action_wp gts_wp crunch_wps
   simp: crunch_simps
   ignore: set_scheduler_action)

context DetSchedSchedule_AI begin

crunch handle_fault_reply
  for not_queued[wp]: "not_queued t :: det_state \<Rightarrow> _"

crunch handle_fault_reply
  for sched_act_not[wp]: "scheduler_act_not t :: det_state \<Rightarrow> _"

crunch handle_fault_reply
  for cur[wp]: "cur_tcb :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch empty_slot_ext, cap_delete_one
  for weak_valid_sched_action[wp]: "weak_valid_sched_action :: det_state \<Rightarrow> _"
  (wp: crunch_wps set_thread_state_runnable_weak_valid_sched_action
       set_bound_notification_weak_valid_sched_action
   simp: cur_tcb_def unless_def)

lemma do_reply_transfer_not_queued[wp]:
  "\<lbrace>not_queued t and invs and st_tcb_at active t and scheduler_act_not t and
    K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. not_queued t :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp cap_delete_one_not_queued hoare_vcg_if_lift | wpc |
         clarsimp split del: if_split | wp (once) hoare_drop_imps)+
   apply (simp add: invs_def valid_state_def valid_pspace_def)+
  done

lemma do_reply_transfer_schedact_not[wp]:
  "\<lbrace>scheduler_act_not t and K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. scheduler_act_not t :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc | clarsimp split del: if_split |
         wp (once) hoare_drop_imps)+
  done

end

lemma assert_false:"\<lbrace>\<lambda>s. \<not> P\<rbrace> assert P \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply wp
  apply simp
  done

lemma do_reply_transfer_add_assert:
  assumes a: "\<lbrace>st_tcb_at awaiting_reply receiver and P\<rbrace>
               do_reply_transfer sender receiver slot grant
              \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> do_reply_transfer sender receiver slot grant \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "st_tcb_at awaiting_reply receiver s")
   apply (rule hoare_pre)
    apply (wp a)
   apply simp
  apply (simp add: do_reply_transfer_def)
  apply (rule bind_wp)
   apply (rule bind_wp)
    prefer 2
    apply (rule assert_false)
   apply simp
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: get_tcb_def pred_tcb_at_def obj_at_def
                  split: option.splits kernel_object.splits)
  done

context DetSchedSchedule_AI begin

lemma do_reply_transfer_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and invs and ct_active and scheduler_act_sane\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. ct_not_queued :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule do_reply_transfer_add_assert)
  apply (rule hoare_pre)
   apply (wp ct_not_queued_lift)
  apply (clarsimp simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma do_reply_transfer_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_active\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. scheduler_act_sane :: det_state \<Rightarrow> _\<rbrace>"
  apply (rule do_reply_transfer_add_assert)
  apply (rule hoare_pre)
   apply (wp sch_act_sane_lift)
  apply (clarsimp simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

crunch handle_reply
  for ct_not_queued[wp]: "ct_not_queued :: det_state \<Rightarrow> _"
crunch handle_reply
  for scheduler_act_sane[wp]: "scheduler_act_sane :: det_state \<Rightarrow> _"

end

locale DetSchedSchedule_AI_handle_hypervisor_fault = DetSchedSchedule_AI +
  assumes handle_hyp_fault_valid_sched[wp]:
    "\<And>t fault.
      \<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
          and (ct_active or ct_idle)\<rbrace>
        handle_hypervisor_fault t fault
      \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  assumes handle_reserved_irq_valid_sched' [wp]:
    "\<And>irq.
      \<lbrace>valid_sched and invs and
         (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
        handle_reserved_irq irq
      \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_interrupt irq \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_interrupt_def
  by (wpsimp wp: get_cap_wp hoare_drop_imps hoare_vcg_all_lift|rule conjI)+

lemma set_scheduler_action_switch_not_cur_thread [wp]:
  "\<lbrace>\<lambda>s. True\<rbrace> set_scheduler_action (switch_thread target) \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  unfolding set_scheduler_action_def
  by wp (simp add: not_cur_thread_def)

lemma possible_switch_to_not_cur_thread [wp]:
  "\<lbrace>not_cur_thread t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. not_cur_thread t\<rbrace>"
  unfolding possible_switch_to_def
  apply (rule hoare_pre)
   apply (wp hoare_vcg_imp_lift|wpc)+
  apply clarsimp
  done

crunch handle_recv
  for not_cur_thread[wp]: "not_cur_thread target :: det_state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

crunch handle_recv
  for it[wp]: "\<lambda>s::det_ext state. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma handle_event_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>rv. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def handle_call_def)
            apply ((rule hoare_pre, wp handle_invocation_valid_sched handle_recv_valid_sched'
              handle_reply_valid_sched
              | fastforce simp: invs_valid_objs invs_sym_refs valid_sched_ct_not_queued)+)[5]
       apply (wp handle_fault_valid_sched hvmf_active hoare_drop_imps hoare_vcg_disj_lift
                 handle_recv_valid_sched' handle_reply_valid_sched hoare_vcg_all_lift|
              wpc |
              clarsimp simp: ct_in_state_def valid_sched_ct_not_queued |
              fastforce simp: valid_fault_def)+
  done

crunch activate_thread
  for valid_list[wp]: valid_list
crunch guarded_switch_to, switch_to_idle_thread, choose_thread
  for valid_list[wp]: valid_list
  (wp: crunch_wps)

end

lemma next_domain_valid_list[wp]:
  "next_domain \<lbrace>valid_list\<rbrace>"
  unfolding next_domain_def Let_def
  apply (fold reset_work_units_def)
  apply (wpsimp | simp add: reset_work_units_def)+
  done

context DetSchedSchedule_AI_handle_hypervisor_fault begin

crunch schedule_choose_new_thread
  for valid_list[wp]: valid_list

lemma schedule_valid_list[wp]: "\<lbrace>valid_list\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: Schedule_A.schedule_def)
  apply (wp add: tcb_sched_action_valid_list gts_wp hoare_drop_imps
         | wpc | simp)+
  done

lemma call_kernel_valid_list[wp]: "\<lbrace>valid_list\<rbrace> call_kernel e \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: call_kernel_def)
  by (wp | simp)+

lemma call_kernel_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_active or ct_idle)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     call_kernel e
   \<lbrace>\<lambda>_. valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp schedule_valid_sched activate_thread_valid_sched | simp)+
     apply (rule_tac Q'="\<lambda>rv. invs" in hoare_strengthen_post)
      apply wp
     apply (erule invs_valid_idle)
    apply (rule hoare_strengthen_post[where Q'="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> valid_sched s \<and> invs s"])
     apply (wpsimp wp: getActiveIRQ_neq_non_kernel)
    apply auto[1]
   apply (rule_tac Q'="\<lambda>rv. valid_sched and invs" and
                   E'="\<lambda>rv. valid_sched and invs" in hoare_strengthen_postE)
     apply (rule valid_validE)
     apply (wp handle_event_valid_sched)
    apply (force intro: active_from_running)+
  done

end

end
