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

lemma set_tcb_queue_wp[wp]: "\<lbrace>\<lambda>s. P (ready_queues_update (\<lambda>_ t' p. if t' = t \<and> p = prio then queue else ready_queues s t' p) s)\<rbrace> set_tcb_queue t prio queue \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: set_tcb_queue_def)
  apply wp
done

lemma get_tcb_queue_wp[wp]: "\<lbrace>\<lambda>s. P (ready_queues s t p) s\<rbrace> get_tcb_queue t p \<lbrace>P\<rbrace>"
  apply (simp add: get_tcb_queue_def)
  apply wp
  done

crunch valid_etcbs[wp]: tcb_sched_action "valid_etcbs"

lemma enqueue_distinct[intro!]: "distinct queue \<Longrightarrow> distinct (tcb_sched_enqueue thread queue)"
  apply (simp add: tcb_sched_enqueue_def)
  done

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 resume_cur_thread ekh kh"
  "weak_valid_sched_action_2 choose_new_thread ekh kh"
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

lemma tcb_sched_action_enqueue_valid_queues[wp]:
  "\<lbrace>valid_queues and st_tcb_at runnable thread\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply simp
  apply (clarsimp simp: valid_queues_def2 etcb_at_def tcb_sched_enqueue_def is_etcb_at_def
                 split: option.split)
  done

lemma tcb_sched_action_append_valid_queues[wp]:
  "\<lbrace>valid_queues and st_tcb_at runnable thread\<rbrace>
     tcb_sched_action tcb_sched_append thread \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: valid_queues_def2 etcb_at_def tcb_sched_append_def is_etcb_at_def
         split: option.split)
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

crunch is_activatable[wp]: tcb_sched_action "is_activatable t"

crunch weak_valid_sched_action[wp]: tcb_sched_action "weak_valid_sched_action"

crunch valid_sched_action[wp]: tcb_sched_action valid_sched_action

crunch ct_in_cur_domain[wp]: tcb_sched_action ct_in_cur_domain

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
      valid_etcbs_2 ekh kh \<and> valid_queues_2 queues ekh kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_2 sa ekh kh ct cdom \<and> ct_in_cur_domain_2 ct it sa cdom ekh \<and> valid_idle_etcb_2 ekh"

abbreviation valid_sched_except_blocked :: "det_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked s \<equiv> valid_sched_except_blocked_2 (ready_queues s) (ekheap s) (scheduler_action s) (cur_domain s) (kheap s) (cur_thread s) (idle_thread s)"

crunch etcb_at[wp]: tcb_sched_action "etcb_at P t"

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

crunch valid_etcbs[wp]: set_scheduler_action "valid_etcbs"

crunch valid_queues[wp]: set_scheduler_action "valid_queues"

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

crunch etcb_at[wp]: set_scheduler_action "etcb_at P t"

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

lemma set_scheduler_action_cnt_weak_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def simple_sched_action_def split: scheduler_action.splits | wp set_scheduler_action_cnt_valid_blocked)+

crunch valid_etcbs[wp]: reschedule_required "valid_etcbs"

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

crunch etcb_at[wp]: reschedule_required "etcb_at P t"

lemma reschedule_required_valid_sched:
  "\<lbrace>valid_etcbs and valid_queues and weak_valid_sched_action and valid_blocked and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_valid_blocked)+

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

lemma set_thread_state_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | wpc | simp add: set_thread_state_ext_def set_object_def)+
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_if_split
                   dest: get_tcb_st_tcb_at)
  done

lemma set_bound_notification_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_if_split
                   dest: get_tcb_st_tcb_at)
  done

lemma set_thread_state_runnable_valid_queues:
  "\<lbrace>valid_queues and K (runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | wpc | simp add: set_thread_state_ext_def set_object_def)+
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  done

lemma set_bound_notification_valid_queues:
  "\<lbrace>valid_queues\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2)
  done

lemma set_thread_state_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp gts_wp)+
  done

lemma set_bound_notification_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_bound_notification ref ntfn \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def | wp)+
  done

lemma set_thread_state_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def |
         wp set_scheduler_action_wp gts_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split
                        pred_tcb_at_def obj_at_def)
  done

lemma set_bound_notification_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_bound_notification ref ntfn
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_thread_state_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp gts_wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split)
  done

lemma set_thread_state_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp set_scheduler_action_wp gts_wp)+
  done

lemma set_bound_notification_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_bound_notification ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp gbn_wp)+
  done

lemma set_bound_notification_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action\<rbrace>
      set_bound_notification ref ntfnptr
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def | wp)+
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
  apply (simp add: set_thread_state_ext_def set_object_def |
        wp set_scheduler_action_wp gts_wp)+
  done

lemma set_bound_notification_cur_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     set_bound_notification ref ts \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (simp add: set_object_def |
        wp set_scheduler_action_wp gbn_wp)+
  done

crunch etcb_at[wp]: set_thread_state, set_bound_notification, get_bound_notification "etcb_at P t"

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
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  apply (simp only: st_tcb_at_kh_if_split)
  apply (simp add: st_tcb_def2 split: if_split_asm)
  done

crunch valid_blocked[wp]: get_bound_notification "valid_blocked"

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
  apply (simp add: set_thread_state_ext_def set_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wp gts_wp)+
  apply (clarsimp simp: valid_blocked_def valid_blocked_except_def st_tcb_at_def obj_at_def)
  done

(* as user schedule invariants *)

lemma as_user_valid_etcbs[wp]: "\<lbrace>valid_etcbs\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  by (fastforce simp: valid_etcbs_def st_tcb_at_kh_if_split dest: get_tcb_st_tcb_at)

lemma as_user_valid_queues[wp]: "\<lbrace>valid_queues\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2)
  apply (drule get_tcb_SomeD, auto)
  done

lemma as_user_weak_valid_sched_action[wp]: "\<lbrace>weak_valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (drule get_tcb_SomeD, auto)

lemma as_user_is_activatable[wp]: "\<lbrace>is_activatable t\<rbrace> as_user ptr s \<lbrace>\<lambda>_. is_activatable t\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  by (drule get_tcb_SomeD, auto)

lemma as_user_valid_sched_action[wp]: "\<lbrace>valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_sched_action_def st_tcb_at_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: is_activatable_def st_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
   apply (drule get_tcb_SomeD, clarsimp)
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_def obj_at_def st_tcb_at_kh_if_split)
  apply (drule get_tcb_SomeD, clarsimp)
  done

lemma as_user_ct_in_cur_domain[wp]: "\<lbrace>ct_in_cur_domain\<rbrace> as_user ptr s \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (simp add: as_user_def set_object_def | wpc | wp)+

lemma as_user_valid_idle_etcb[wp]: "\<lbrace>valid_idle_etcb\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  by (simp add: as_user_def set_object_def | wpc | wp)+

lemma as_user_valid_blocked[wp]: "\<lbrace>valid_blocked\<rbrace> as_user ptr s \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=ptr in spec)
  by (drule get_tcb_SomeD, auto)

definition ct_in_q where
  "ct_in_q s \<equiv> st_tcb_at runnable (cur_thread s) s \<longrightarrow> (\<exists>d p. cur_thread s \<in> set (ready_queues s d p))"

locale DetSchedSchedule_AI =
  assumes arch_switch_to_idle_thread_valid_etcbs'[wp]:
    "\<lbrace>valid_etcbs\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  assumes arch_switch_to_thread_valid_etcbs'[wp]:
    "\<And>t. \<lbrace>valid_etcbs\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_queues'[wp]:
    "\<lbrace>valid_queues\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  assumes arch_switch_to_thread_valid_queues'[wp]:
    "\<And>t. \<lbrace>valid_queues\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  assumes arch_switch_to_idle_thread_weak_valid_sched_action'[wp]:
    "\<lbrace>weak_valid_sched_action\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  assumes arch_switch_to_thread_weak_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>weak_valid_sched_action\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  assumes switch_to_idle_thread_ct_not_in_q[wp]:
    "\<lbrace>valid_queues and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  assumes switch_to_idle_thread_valid_sched_action[wp]:
    "\<lbrace>valid_sched_action and valid_idle\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  assumes switch_to_idle_thread_ct_in_cur_domain[wp]:
    "\<lbrace>\<top>\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  assumes arch_switch_to_thread_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  assumes arch_switch_to_thread_is_activatable'[wp]:
    "\<And>t t'. \<lbrace>is_activatable t'\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. is_activatable t'\<rbrace>"
  assumes arch_switch_to_thread_valid_sched_action'[wp]:
    "\<And>t. \<lbrace>valid_sched_action\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  assumes arch_switch_to_thread_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes arch_switch_to_thread_ct_in_cur_domain_2[wp]:
    "\<And>t' t.
      \<lbrace>\<lambda>s. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>
        arch_switch_to_thread t
      \<lbrace>\<lambda>_ s. ct_in_cur_domain_2 t' (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>"
  assumes arch_switch_to_thread_valid_blocked[wp]:
    "\<And>t. \<lbrace>valid_blocked and ct_in_q\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  assumes arch_switch_to_thread_etcb_at'[wp]:
    "\<And>P t' t. \<lbrace>etcb_at P t'\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. etcb_at P t'\<rbrace>"
  assumes arch_switch_to_idle_thread_valid_idle[wp]:
    "\<lbrace>valid_idle :: det_ext state \<Rightarrow> bool\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes switch_to_idle_thread_ct_not_queued[wp]:
    "\<lbrace>valid_queues and valid_etcbs and valid_idle\<rbrace>
      switch_to_idle_thread
     \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  assumes switch_to_idle_thread_valid_blocked[wp]:
    "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
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
    "\<And>P t. \<lbrace>etcb_at P t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. etcb_at P t\<rbrace>"
  assumes switch_to_idle_thread_cur_thread_idle_thread [wp]:
    "\<lbrace>\<top> :: det_ext state \<Rightarrow> bool\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_ s. cur_thread s = idle_thread s\<rbrace>"
  assumes arch_switch_to_idle_thread_scheduler_action'[wp]:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  assumes arch_finalise_cap_ct_not_in_q'[wp]:
    "\<And>acap final. \<lbrace>ct_not_in_q\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  assumes arch_finalise_cap_valid_etcbs'[wp]:
    "\<And>acap final. \<lbrace>valid_etcbs\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  assumes arch_finalise_cap_simple_sched_action'[wp]:
    "\<And>acap final. \<lbrace>simple_sched_action\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  assumes arch_finalise_cap_valid_sched'[wp]:
    "\<And>acap final. \<lbrace>valid_sched\<rbrace> arch_finalise_cap acap final \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes arch_tcb_set_ipc_buffer_valid_sched'[wp]:
    "\<And>target ptr. \<lbrace>valid_sched\<rbrace> arch_tcb_set_ipc_buffer target ptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes handle_arch_fault_reply_valid_sched'[wp]:
    "\<And>f t x y. \<lbrace>valid_sched\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes activate_thread_valid_sched:
    "\<lbrace>valid_sched\<rbrace> activate_thread \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes arch_perform_invocation_valid_sched[wp]:
    "\<And>i.
      \<lbrace>invs and valid_sched and ct_active and valid_arch_inv i\<rbrace>
        arch_perform_invocation i
      \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  assumes arch_invoke_irq_control_valid_sched'[wp]:
    "\<And>i. \<lbrace>valid_sched\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes handle_vm_fault_valid_sched'[wp]:
    "\<And>t f. \<lbrace>valid_sched\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes handle_vm_fault_not_queued'[wp]:
    "\<And>t' t f. \<lbrace>not_queued t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. not_queued t'\<rbrace>"
  assumes handle_vm_fault_scheduler_act_not'[wp]:
    "\<And>t' t f. \<lbrace>scheduler_act_not t'\<rbrace> handle_vm_fault t f \<lbrace>\<lambda>_. scheduler_act_not t'\<rbrace>"
  assumes handle_arch_fault_reply_not_queued'[wp]:
    "\<And>t' f t x y. \<lbrace>not_queued t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. not_queued t'\<rbrace>"
  assumes handle_arch_fault_reply_scheduler_act_not'[wp]:
    "\<And>t' f t x y. \<lbrace>scheduler_act_not t'\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. scheduler_act_not t'\<rbrace>"
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
  assumes prepare_thread_delete_ct_not_in_q'[wp]:
    "\<And>t. \<lbrace>ct_not_in_q\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  assumes prepare_thread_delete_valid_etcbs'[wp]:
    "\<And>t. \<lbrace>valid_etcbs\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  assumes prepare_thread_delete_simple_sched_action'[wp]:
    "\<And>t. \<lbrace>simple_sched_action\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  assumes prepare_thread_delete_valid_sched'[wp]:
    "\<And>t. \<lbrace>valid_sched\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. valid_sched\<rbrace>"

context DetSchedSchedule_AI begin

crunch valid_etcbs[wp]: switch_to_idle_thread, switch_to_thread valid_etcbs
  (simp: whenE_def)

crunch valid_queues[wp]: switch_to_idle_thread, switch_to_thread valid_queues
  (simp: whenE_def ignore: set_tcb_queue tcb_sched_action)

crunch weak_valid_sched_action[wp]:
  switch_to_idle_thread, switch_to_thread "weak_valid_sched_action"
  (simp: whenE_def)

end

lemma tcb_sched_action_dequeue_ct_not_in_q_2_ct_upd:
  "\<lbrace>valid_queues\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. ct_not_in_q_2 (ready_queues s) (scheduler_action s) thread\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (fastforce simp: etcb_at_def ct_not_in_q_def valid_queues_def
                         tcb_sched_dequeue_def not_queued_def
                   split: option.split)
  done

lemma tcb_sched_action_dequeue_valid_sched_action_2_ct_upd:
  "\<lbrace>valid_sched_action and
       (\<lambda>s. is_activatable_2 thread (scheduler_action s) (kheap s))\<rbrace>
     tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>r s. valid_sched_action_2 (scheduler_action s) (ekheap s) (kheap s) thread (cur_domain s)\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (clarsimp simp: etcb_at_def valid_sched_action_def split: option.split)
  done

context DetSchedSchedule_AI begin

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply (wp | wpc)+
  apply clarsimp
  apply (fastforce simp: valid_sched_def valid_etcbs_def valid_queues_def
                         valid_sched_action_def is_activatable_def
                         weak_valid_sched_action_def st_tcb_at_kh_if_split
                         st_tcb_def2 valid_blocked_def)
  done

lemma switch_to_thread_ct_not_queued[wp]:
  "\<lbrace>valid_queues\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_thread_def)
  including no_pre
  apply wp
     prefer 4
     apply (rule get_wp)
    prefer 3
    apply (rule assert_inv)
   prefer 2
   apply (rule arch_switch_to_thread_valid_queues)
  apply (simp add: tcb_sched_action_def
                   tcb_sched_dequeue_def | wp)+
  apply (clarsimp simp add: valid_queues_def etcb_at_def not_queued_def
                       split: option.splits)
  done

end

lemma ct_not_in_q_def2:
  "ct_not_in_q_2 queues sa ct = (sa = resume_cur_thread \<longrightarrow> (\<forall>d p. ct \<notin> set (queues d p)))"
  by (fastforce simp add: ct_not_in_q_def not_queued_def)

context DetSchedSchedule_AI begin

lemma switch_to_thread_ct_not_in_q[wp]:
  "\<lbrace>valid_queues\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: ct_not_in_q_def2 not_queued_def[symmetric])
  apply (wp hoare_drop_imps | simp)+
  done

lemma switch_to_thread_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and is_activatable t\<rbrace>
     switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wpsimp wp: tcb_sched_action_dequeue_valid_sched_action_2_ct_upd simp: switch_to_thread_def)

end

lemma tcb_sched_action_dequeue_ct_in_cur_domain':
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
  \<lbrace>\<lambda>_ s. ct_in_cur_domain (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (simp add: etcb_at_def split: option.split)
  done

context DetSchedSchedule_AI begin

crunch ct_in_cur_domain_2[wp]: as_user
  "\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)"
  (simp: whenE_def)

lemma switch_to_thread_ct_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. ct_in_cur_domain_2 thread (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)\<rbrace>
  switch_to_thread thread \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
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
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_at_def obj_at_def)
  apply (drule_tac x=tp in spec)
  apply (drule get_tcb_SomeD, simp)
  apply (simp add: ct_in_q_def)
  apply (case_tac "tp = cur_thread s"; clarsimp simp: st_tcb_at_def obj_at_def)
  done
end

crunch ct_in_q[wp]: do_machine_op ct_in_q

lemma do_machine_op_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_blocked and ct_in_q\<rbrace>"
  by (wpsimp | auto)+

context DetSchedSchedule_AI begin

lemma switch_to_thread_valid_blocked[wp]:
  "\<lbrace>valid_blocked and ct_in_q\<rbrace> switch_to_thread thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp|wpc)+
     prefer 4
     apply (rule get_wp)
    prefer 3
    apply (rule assert_inv)
   prefer 2
   apply (rule arch_switch_to_thread_valid_blocked)
  by (wp tcb_sched_action_dequeue_ct_in_cur_domain' tcb_sched_action_dequeue_valid_blocked')

crunch etcb_at[wp]: switch_to_thread "etcb_at P t"

lemma switch_to_thread_valid_sched:
  "\<lbrace>is_activatable t and in_cur_domain t and valid_sched_action and valid_etcbs and valid_queues and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
    switch_to_thread t
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp | simp add: ct_in_cur_domain_2_def)+
  done

crunch valid_idle[wp]: switch_to_idle_thread "valid_idle :: det_ext state \<Rightarrow> bool"

crunch scheduler_action[wp]: switch_to_thread "\<lambda>s. P (scheduler_action (s :: det_ext state))"

end

crunch valid_etcbs[wp]: update_cdt_list "valid_etcbs"
crunch valid_queues[wp]: update_cdt_list "valid_queues"
crunch ct_not_in_q[wp]: update_cdt_list "ct_not_in_q"
crunch weak_valid_sched_action[wp]: update_cdt_list "weak_valid_sched_action"
crunch valid_sched_action[wp]: update_cdt_list "valid_sched_action"
crunch valid_blocked[wp]: update_cdt_list valid_blocked
crunch valid_sched[wp]: update_cdt_list "valid_sched"

crunch valid_etcbs[wp]: set_cdt, set_cap valid_etcbs
  (wp: valid_etcbs_lift set_cap_typ_at)
crunch valid_queues[wp]: set_cdt, set_cap valid_queues
  (wp: valid_queues_lift)
crunch ct_not_in_q[wp]: set_cdt, set_cap ct_not_in_q
  (wp: ct_not_in_q_lift)
crunch weak_valid_sched_action[wp]: set_cdt, set_cap weak_valid_sched_action
  (wp: weak_valid_sched_action_lift)
crunch valid_sched_action[wp]: set_cdt, set_cap valid_sched_action
  (wp: valid_sched_action_lift)
crunch valid_blocked[wp]: set_cdt, set_cap valid_blocked
  (wp: valid_blocked_lift)
crunch valid_sched[wp]: set_cdt, set_cap  valid_sched
  (wp: valid_sched_lift set_cap_typ_at)

crunch ct_not_in_q[wp]: cap_insert ct_not_in_q
  (wp: hoare_drop_imps)

crunch weak_valid_sched_action[wp]: cap_insert weak_valid_sched_action
  (wp: hoare_drop_imps)

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

crunch valid_idle[wp]: next_domain valid_idle

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
      apply (simp add: next_thread_def
                       max_non_empty_queue_def)
      done}
  moreover
  { assume d: "{prio. queues prio \<noteq> []} \<noteq> {}"
    from a b have ?thesis
      apply (clarsimp simp: next_thread_def
                            max_non_empty_queue_def
                            Max_insert[OF finite_word d])
      apply (clarsimp simp add: max_def)
      done }
  ultimately show ?thesis by blast
qed

lemma enqueue_nonempty:
  "\<lbrace>\<top>\<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. (\<exists>d prio. ready_queues s d prio \<noteq> [])\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def
                  split: option.splits)
  done

lemma next_thread_queued: "queues p \<noteq> [] \<Longrightarrow> \<exists>p. next_thread queues \<in> set (queues p)"
  apply (clarsimp simp: next_thread_def max_non_empty_queue_def)
  apply (rule_tac x="Max {prio. queues prio \<noteq> []}" in exI)
  apply (rule Max_prop)
   apply simp
  apply blast
  done

context DetSchedSchedule_AI begin

crunch etcb_at[wp]: switch_to_idle_thread "etcb_at P t"

lemma switch_to_idle_thread_valid_sched:
  "\<lbrace>valid_sched_action and valid_idle and valid_queues and valid_etcbs and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
     switch_to_idle_thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp)+

crunch etcb_at[wp]: choose_thread "etcb_at P t"
  (wp: crunch_wps)

lemma choose_thread_valid_sched[wp]:
  "\<lbrace>valid_sched_action and valid_idle and valid_etcbs and valid_queues and valid_blocked and ct_in_q and valid_idle_etcb\<rbrace>
     choose_thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
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

crunch valid_etcbs: next_domain valid_etcbs (simp: Let_def)
crunch valid_queues: next_domain valid_queues (simp: Let_def)
crunch valid_blocked: next_domain valid_blocked (simp: Let_def)
crunch ct_in_q: next_domain ct_in_q (simp: Let_def ct_in_q_def)
crunch ct_not_in_q: next_domain ct_not_in_q (simp: Let_def)

lemma next_domain_valid_sched_action:
  "\<lbrace>\<lambda>s. scheduler_action s = choose_new_thread\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: next_domain_def thread_set_domain_def ethread_set_def set_eobject_def)
  apply wp
  apply (clarsimp simp: Let_def valid_sched_action_def weak_valid_sched_action_def
                        get_etcb_def etcb_at_def)
  done

lemma tcb_sched_action_dequeue_in_cur_domain:
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
   \<lbrace>\<lambda>_ s. in_cur_domain (cur_thread s) s\<rbrace>"
  apply (simp add: switch_to_thread_def | wp tcb_sched_action_dequeue_in_cur_domain)+
  done
end

lemma tcb_sched_enqueue_cur_ct_in_q:
  "\<lbrace>\<lambda>s. cur = cur_thread s\<rbrace> tcb_sched_action tcb_sched_enqueue cur \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (force simp: etcb_at_def ct_in_q_def tcb_sched_enqueue_def split: option.splits)
  done

context DetSchedSchedule_AI begin
crunch scheduler_action[wp]: switch_to_idle_thread, next_domain "\<lambda>s. P (scheduler_action s)"
  (simp: Let_def)
end

lemma set_scheduler_action_rct_switch_thread_valid_blocked:
  "\<lbrace>valid_blocked and (\<lambda>s. scheduler_action s = switch_thread (cur_thread s))\<rbrace>
   set_scheduler_action resume_cur_thread \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: valid_blocked_def, wp set_scheduler_action_wp)
  apply clarsimp
  done

crunch etcb_at[wp]: set_scheduler_action "etcb_at P t"

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

crunch valid_idle_etcb[wp]: next_domain "valid_idle_etcb"
  (simp: Let_def)

context DetSchedSchedule_AI begin

lemma schedule_valid_sched:
  "\<lbrace>valid_sched and valid_idle\<rbrace> schedule \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp only: schedule_def choose_thread_def next_thread_def[symmetric])
  apply wp
     apply wpc (* 3 cases *)
       apply wp
      apply (wp switch_to_thread_valid_sched guarded_switch_to_lift
                stt_activatable[simplified ct_in_state_def]
                tcb_sched_enqueue_in_cur_domain hoare_disjI1
                tcb_sched_action_enqueue_valid_blocked
                tcb_sched_enqueue_cur_ct_in_q
                set_scheduler_action_rct_switch_thread_valid_sched
                switch_to_thread_sched_act_is_cur)
     apply (wp del: hoare_when_wp
               add: switch_to_idle_thread_valid_sched
               stit_activatable'[simplified ct_in_state_def]
               hoare_disjI2[OF switch_to_idle_thread_cur_thread_idle_thread]
               guarded_switch_to_lift switch_to_thread_valid_sched
               stt_activatable[simplified ct_in_state_def]
               hoare_disjI1[OF switch_to_thread_cur_in_cur_domain]
               hoare_vcg_all_lift set_scheduler_action_rct_valid_sched)
       apply (rule_tac Q="\<lambda>_. valid_queues and valid_etcbs and valid_idle and valid_sched_action and valid_blocked and ct_in_q and simple_sched_action and valid_idle_etcb" in hoare_post_imp)
        apply (clarsimp simp: valid_queues_def is_activatable_def in_cur_domain_def)
        apply (drule next_thread_queued)
        apply clarsimp
        apply (drule_tac x="cur_domain s" in spec)
        apply (drule_tac x=p in spec)
        apply (fastforce simp: st_tcb_def2 ct_in_cur_domain_2_def in_cur_domain_def etcb_at_def split: option.splits)
       apply (wp next_domain_valid_queues next_domain_valid_etcbs next_domain_valid_sched_action next_domain_valid_blocked next_domain_ct_in_q hoare_vcg_all_lift)[1]
      apply wp
     apply (rule_tac Q="\<lambda>_ s. valid_sched s \<and> valid_idle s \<and> valid_blocked s \<and> ct_in_q s \<and> scheduler_action s = choose_new_thread \<and> valid_idle_etcb s" in hoare_post_imp)
      apply (simp add: valid_sched_def valid_blocked_def)
     apply (wp gts_wp tcb_sched_action_enqueue_valid_blocked tcb_sched_enqueue_cur_ct_in_q)+
  apply (auto simp: valid_sched_def weak_valid_sched_action_def
                    valid_etcbs_def switch_in_cur_domain_def
                    valid_sched_action_def
                    not_cur_thread_def valid_blocked_def valid_blocked_except_def ct_in_q_def
                    etcb_at_def st_tcb_def2
             split: option.splits)
  done

crunch ct_not_in_q[wp]: finalise_cap ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

end

lemma set_endpoint_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_endpoint_def)+

lemma set_endpoint_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (wp hoare_drop_imps valid_queues_lift | simp add: set_endpoint_def)+

lemma set_endpoint_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift | simp add: set_endpoint_def)+

lemma set_endpoint_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps switch_in_cur_domain_lift | simp add: set_endpoint_def)+

lemma set_endpoint_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps ct_in_cur_domain_lift | simp add: set_endpoint_def)+

lemma set_endpoint_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_endpoint_def)+

lemma set_endpoint_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_lift | simp add: set_endpoint_def)+

lemma set_notification_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_notification_def)+

lemma set_notification_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> set_notification ptr aeep \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (wp hoare_drop_imps valid_queues_lift | simp add: set_notification_def)+

lemma set_notification_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift | simp add: set_notification_def)+

lemma set_notification_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps switch_in_cur_domain_lift | simp add: set_notification_def)+

lemma set_notification_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  by (wp hoare_drop_imps ct_in_cur_domain_lift | simp add: set_notification_def)+

lemma set_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift | simp add: set_notification_def)+

lemma set_notification_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  by (wp hoare_drop_imps valid_blocked_lift | simp add: set_notification_def)+

crunch etcb_at[wp]: set_endpoint "etcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (wp mapM_x_wp set_thread_state_runnable_valid_queues sts_st_tcb_at' hoare_drop_imps
          set_thread_state_runnable_weak_valid_sched_action hoare_vcg_all_lift
          set_thread_state_valid_blocked_except
          tcb_sched_action_enqueue_valid_blocked
          reschedule_required_valid_sched
     | wpc
     | rule subset_refl | simp)+
    apply (simp_all add: valid_sched_def valid_sched_action_def)
    done

crunch etcb_at[wp]: set_notification "etcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_signals_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (wp mapM_x_wp set_thread_state_runnable_valid_queues sts_st_tcb_at' hoare_drop_imps
          set_thread_state_runnable_weak_valid_sched_action hoare_vcg_all_lift
          set_thread_state_valid_blocked_except
          tcb_sched_action_enqueue_valid_blocked
          reschedule_required_valid_sched
       | wpc
       | rule subset_refl | simp)+
   apply (simp_all add: valid_sched_def valid_sched_action_def)
  done

lemma thread_set_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: thread_set_def)+

lemma thread_set_valid_queues:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
    \<lbrace>valid_queues\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (wp hoare_drop_imps valid_queues_lift thread_set_no_change_tcb_state |
      simp add: thread_set_def)+

lemma thread_set_weak_valid_sched_action:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps weak_valid_sched_action_lift thread_set_no_change_tcb_state
        | simp add: thread_set_def)+

lemma thread_set_not_state_valid_sched:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   \<lbrace>valid_sched\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift thread_set_no_change_tcb_state |
      simp add: thread_set_def)+

lemma unbind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_notification ntfnptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptra, simp, wp, simp)
  apply (clarsimp)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp])
  apply (wp set_bound_notification_valid_sched, clarsimp)
  done

context DetSchedSchedule_AI begin
crunch valid_etcbs[wp]: finalise_cap valid_etcbs
  (wp: hoare_drop_imps hoare_unless_wp select_inv mapM_x_wp mapM_wp subset_refl
       if_fun_split simp: crunch_simps ignore: set_object)
end

crunch valid_sched[wp]: cap_swap_for_delete, empty_slot, cap_delete_one valid_sched
  (simp: unless_def)

lemma reply_cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (wp select_wp hoare_drop_imps thread_set_not_state_valid_sched | simp)+
  done

lemma st_tcb_at_not:
  "st_tcb_at (\<lambda>st. \<not> P st) t s = (\<not> st_tcb_at P t s \<and> tcb_at t s)"
  apply (clarsimp simp: not_pred_tcb)
  apply (fastforce simp: st_tcb_at_tcb_at)
  done

lemma set_thread_state_not_runnable_valid_queues:
  "\<lbrace>valid_queues and ct_not_in_q and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split ct_not_in_q_def
                         st_tcb_at_not)
  done

lemma set_thread_state_not_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp gts_wp)+
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
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp)+
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

lemma cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_ipc_def get_thread_state_def thread_get_def)
  apply (wp | wpc)+
  apply (fastforce intro: st_tcb_at_get_lift)
  done

(* valid_queues with thread not runnable *)
lemma tcb_sched_action_dequeue_strong_valid_sched:
  "\<lbrace>valid_etcbs and ct_not_in_q and valid_sched_action and ct_in_cur_domain and
    valid_blocked and st_tcb_at (\<lambda>st. \<not> runnable st) thread and
    (\<lambda>es. \<forall>d p. (\<forall>t\<in>set (ready_queues es d p). is_etcb_at t es \<and>
        etcb_at (\<lambda>t. tcb_priority t = p \<and> tcb_domain t = d) t es \<and>
        (t \<noteq> thread \<longrightarrow> st_tcb_at runnable t es)) \<and> distinct (ready_queues es d p)) and
    valid_idle_etcb\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (clarsimp simp: etcb_at_def valid_sched_def split: option.split)
  apply (rule conjI)
   apply (fastforce simp: etcb_at_def is_etcb_at_def valid_queues_def2 tcb_sched_dequeue_def)
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

crunch simple_sched_action[wp]: tcb_sched_action, update_cdt_list simple_sched_action

context DetSchedSchedule_AI begin

crunch simple_sched_action[wp]: finalise_cap simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl
   simp: unless_def if_fun_split)

lemma suspend_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> suspend t \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
apply (simp add: suspend_def)
apply (rule seq_ext)
 apply (rule_tac R="K $ valid_sched and simple_sched_action" in hoare_strengthen_post[rotated])
  apply (wp tcb_sched_action_dequeue_strong_valid_sched
       | simp)+
    apply (simp add: set_thread_state_def)
    apply (wp gts_wp | wpc |
           simp add: set_thread_state_def set_thread_state_ext_def
                     reschedule_required_def set_scheduler_action_def
                     tcb_sched_action_def set_object_def)+
    apply (simp only: st_tcb_at_kh_simp[symmetric])
    apply (clarsimp simp: valid_sched_def valid_queues_def st_tcb_at_kh_if_split
                          valid_sched_action_def simple_sched_action_def
                          is_activatable_def valid_blocked_def
                    split: scheduler_action.splits)+
    done

crunch valid_sched[wp]: finalise_cap valid_sched
  (wp: crunch_wps simp: crunch_simps)

end

crunch simple_sched_action[wp]: cap_swap_for_delete, cap_insert simple_sched_action
  (wp: mapM_wp subset_refl hoare_drop_imps)

context DetSchedSchedule_AI begin

lemma rec_del_valid_sched'[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
    rec_del call
   \<lbrace>\<lambda>rv. valid_sched and simple_sched_action\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wp preemption_point_inv' | simp)+
  done

lemma rec_del_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule rec_del_valid_sched')
  apply simp
  done

lemma rec_del_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> rec_del call \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wp rec_del_preservation preemption_point_inv' | simp)+

crunch valid_sched[wp]: cap_delete valid_sched

crunch simple_sched_action[wp]: cap_delete simple_sched_action

end

lemma ethread_set_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> ethread_set f tptr \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: valid_etcbs_def is_etcb_at_def get_etcb_def)
  done

crunch ct_not_in_q[wp]: ethread_set "ct_not_in_q"

crunch not_cur_thread[wp]: ethread_set, tcb_sched_action "not_cur_thread t"

crunch cur_is_activatable[wp]: ethread_set "\<lambda>s. is_activatable (cur_thread s) s"

lemma ethread_set_not_queued_valid_queues:
  "\<lbrace>valid_queues and not_queued tptr\<rbrace>
     ethread_set f tptr
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def not_queued_def | wp)+
  apply (clarsimp simp: valid_queues_def is_etcb_at_def etcb_at_def)
  done

lemma ethread_set_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def is_etcb_at_def etcb_at_def get_etcb_def)
  done

lemma ethread_set_not_domain_switch_in_cur_domain:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>switch_in_cur_domain\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at_def get_etcb_def)
  done

lemma ethread_set_not_domain_ct_in_cur_domain:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>ct_in_cur_domain\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcb_at_def get_etcb_def)
  done

lemma ethread_set_not_domain_valid_blocked:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>valid_blocked\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  done

lemma ethread_set_not_domain_valid_blocked_except:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>valid_blocked_except ref\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_blocked_except ref\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  done

lemma ethread_set_not_domain_valid_sched_action:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>valid_sched_action\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def | wp ethread_set_not_domain_switch_in_cur_domain)+
  done

lemma ethread_set_valid_idle_etcb:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>valid_idle_etcb\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  apply(simp add: ethread_set_def valid_idle_etcb_def set_eobject_def)
  apply wp
  apply(simp add: etcb_at_def get_etcb_def split: option.splits)
  done

lemma ethread_set_not_queued_valid_sched:
  "(\<And>x. tcb_domain (f x) = tcb_domain x)
  \<Longrightarrow> \<lbrace>valid_sched and not_queued tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_sched_action_def | wp ethread_set_not_queued_valid_queues ethread_set_not_domain_switch_in_cur_domain ethread_set_not_domain_ct_in_cur_domain ethread_set_not_domain_valid_blocked ethread_set_valid_idle_etcb)+
  done

lemma tcb_dequeue_not_queued:
  "\<lbrace>valid_queues\<rbrace> tcb_sched_action tcb_sched_dequeue tptr \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
  apply (simp add: tcb_sched_action_def | wp)+
  apply (clarsimp simp: etcb_at_def tcb_sched_dequeue_def not_queued_def
                        valid_queues_def
                  split: option.splits)
  done

crunch ct_in_state[wp]: set_eobject, set_tcb_queue "ct_in_state P"
  (simp: ct_in_state_def pred_tcb_at_def obj_at_def)

crunch ct_in_state[wp]: tcb_sched_action, ethread_set "ct_in_state P"

crunch not_pred_tcb[wp]: set_eobject, set_tcb_queue "\<lambda>s. \<not> pred_tcb_at proj P t s"
  (simp: ct_in_state_def pred_tcb_at_def obj_at_def)

crunch not_pred_tcb[wp]: tcb_sched_action, ethread_set "\<lambda>s. \<not> pred_tcb_at proj P t s"

lemma ct_in_state_def2: "ct_in_state test s = st_tcb_at test (cur_thread s) s"
   by (simp add: ct_in_state_def)

lemma set_priority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_priority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: set_priority_def thread_set_priority_def)
   apply (wp gts_wp hoare_vcg_if_lift ethread_set_not_queued_valid_queues hoare_vcg_all_lift
             tcb_dequeue_not_queued hoare_vcg_imp_lift hoare_vcg_disj_lift
             tcb_sched_action_enqueue_valid_blocked
             ethread_set_not_domain_valid_sched_action
             ethread_set_not_domain_ct_in_cur_domain
             ethread_set_not_domain_valid_blocked
             ethread_set_not_domain_valid_blocked_except
             ethread_set_not_queued_valid_sched
             tcb_sched_action_dequeue_valid_blocked
             tcb_sched_action_dequeue_valid_blocked_except
             tcb_sched_action_dequeue_valid_sched_not_runnable
             reschedule_required_valid_sched ethread_set_valid_idle_etcb
            
         | simp add: ct_in_state_def2[symmetric])+
  apply (force simp: valid_sched_def valid_sched_action_def
                not_cur_thread_def ct_in_state_def not_pred_tcb st_tcb_at_def obj_at_def)
  done

lemma set_mcpriority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mcpriority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

crunch simple_sched_action[wp]: set_priority,set_mcpriority simple_sched_action

context DetSchedSchedule_AI begin

crunch valid_sched[wp]: arch_tcb_set_ipc_buffer valid_sched

lemma tc_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
      invoke_tcb (ThreadControl a sl b mcp pr e f g)
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  including no_pre
  apply (simp add: split_def set_mcpriority_def cong: option.case_cong)
  apply (rule hoare_vcg_precond_imp)
   apply (wp check_cap_inv thread_set_not_state_valid_sched hoare_vcg_all_lift gts_wp static_imp_wp
         | wpc | simp add: option_update_thread_def)+
   done

end

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  apply (clarsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def switch_in_cur_domain_def valid_blocked_def simple_sched_action_def split: scheduler_action.splits)
  done

lemma possible_switch_to_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable target and (\<lambda>s. \<not> on_same_prio \<longrightarrow> not_cur_thread target s) and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     possible_switch_to target on_same_prio \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: possible_switch_to_def | (wp static_imp_conj_wp static_imp_wp
                       tcb_sched_action_enqueue_valid_blocked
                       reschedule_required_valid_sched
                       set_scheduler_action_swt_weak_valid_sched)+ | wpc)+
  apply (fastforce simp: etcb_at'_def not_cur_thread_2_def valid_sched_def valid_sched_action_def in_cur_domain_def ct_in_cur_domain_2_def valid_blocked_def valid_blocked_except_def split: option.splits)
  done

lemma switch_if_required_to_valid_sched:
  "\<lbrace>valid_sched and not_cur_thread target and st_tcb_at runnable target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace> switch_if_required_to target\<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: switch_if_required_to_def | wp possible_switch_to_valid_sched)+

lemma attempt_switch_to_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace> attempt_switch_to target \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: attempt_switch_to_def | wp possible_switch_to_valid_sched)+

lemma set_sched_action_cnt_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (simp add: set_scheduler_action_def | wp | wpc)+
  apply (simp add: not_cur_thread_def)
  done

lemma reschedule_required_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: reschedule_required_def | wp)+

lemma set_thread_state_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread thread\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv. not_cur_thread thread\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_def set_thread_state_ext_def set_object_def |
         wp gts_wp)+
  done

crunch valid_sched[wp]: setup_reply_master valid_sched

crunch valid_etcbs[wp]: setup_reply_master valid_etcbs

crunch valid_queues[wp]: setup_reply_master valid_queues

crunch ct_not_in_q[wp]: setup_reply_master ct_not_in_q

crunch valid_sched_action[wp]: setup_reply_master valid_sched_action

crunch ct_in_cur_domain[wp]: setup_reply_master ct_in_cur_domain

crunch valid_blocked[wp]: setup_reply_master valid_blocked
crunch not_cur_thread[wp]: empty_slot "not_cur_thread thread"

crunch not_cur_thread[wp]: setup_reply_master, cancel_ipc "not_cur_thread thread"
  (wp: hoare_drop_imps select_wp mapM_x_wp simp: unless_def if_fun_split)

crunch etcb_at[wp]: setup_reply_master "etcb_at P t"

lemma restart_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace> restart thread \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  including no_pre
  apply (simp add: restart_def | wp set_thread_state_runnable_valid_queues
                                    set_thread_state_runnable_valid_sched_action
                                    set_thread_state_valid_blocked_except
                                    sts_st_tcb_at' cancel_ipc_simple2
                                    switch_if_required_to_valid_sched)+
   apply (rule_tac Q="\<lambda>_. valid_sched and not_cur_thread thread and (\<lambda>s. thread \<noteq> idle_thread s)" in hoare_strengthen_post)
    apply wp
   apply (simp add: valid_sched_def)
  apply (simp add: if_fun_split)
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
  done

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply (wp | wpc)+
  apply clarsimp
  by (fastforce simp: valid_sched_def valid_etcbs_def valid_queues_def
                      valid_sched_action_def is_activatable_def
                      weak_valid_sched_action_def st_tcb_at_kh_if_split
                      st_tcb_def2 valid_blocked_def)

crunch valid_sched[wp]: bind_notification "valid_sched"

crunch it[wp]: suspend "\<lambda> s. P (idle_thread s)"
(ignore: tcb_sched_action wp: dxo_wp_weak)

context DetSchedSchedule_AI begin
lemma invoke_tcb_valid_sched[wp]:
  "\<lbrace>invs and valid_sched and simple_sched_action and tcb_inv_wf ti\<rbrace> invoke_tcb ti \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases ti, simp_all only:)
        apply (wp mapM_x_wp | simp | rule subset_refl | clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap | intro impI conjI)+
   apply (rename_tac option)
   apply (case_tac option)
    apply (wp mapM_x_wp | simp | rule subset_refl | clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap | intro impI conjI)+
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

crunch valid_sched[wp]: store_word_offs valid_sched

crunch pred_tcb_at[wp]: set_mrs, as_user "pred_tcb_at proj P t"

crunch exst[wp]: set_mrs, as_user "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

crunch it[wp]: as_user "\<lambda>s. P (idle_thread s)"

crunch valid_etcbs[wp]: as_user valid_etcbs (wp: valid_etcbs_lift)

crunch valid_queues[wp]: as_user valid_queues
  (wp: valid_queues_lift)

crunch ct_not_in_q[wp]: as_user ct_not_in_q
  (wp: ct_not_in_q_lift)

crunch valid_sched_action[wp]: as_user valid_sched_action
  (wp: valid_sched_action_lift)

crunch ct_in_cur_domain[wp]: as_user ct_in_cur_domain
  (wp: ct_in_cur_domain_lift)

crunch valid_sched[wp]: set_mrs valid_sched
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
  "\<lbrace>valid_etcbs and valid_queues and weak_valid_sched_action and (\<lambda>s. case scheduler_action s of switch_thread t \<Rightarrow> valid_blocked_except t s | _ \<Rightarrow> False) and valid_idle_etcb\<rbrace>
    reschedule_required
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: valid_sched_def | wp reschedule_required_switch_valid_blocked | force)+

lemma set_scheduler_action_swt_weak_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  apply (force simp: valid_sched_def ct_not_in_q_def valid_sched_action_def weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def switch_in_cur_domain_def valid_blocked_def valid_blocked_except_def simple_sched_action_def split: scheduler_action.splits)
  done

lemma possible_switch_to_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target and st_tcb_at runnable target and (\<lambda>s. \<not> on_same_prio \<longrightarrow> not_cur_thread target s) and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     possible_switch_to target on_same_prio \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (simp | (wp static_imp_conj_wp reschedule_required_switch_valid_sched
                   tcb_sched_action_enqueue_valid_blocked
                   set_scheduler_action_swt_weak_valid_sched')+ | wpc
             | wp_once hoare_vcg_all_lift)+
          apply (simp add: tcb_sched_action_def)
          apply (wp static_imp_wp)+
  apply (clarsimp simp: etcb_at'_def not_cur_thread_2_def valid_sched_def valid_sched_action_def in_cur_domain_def ct_in_cur_domain_2_def valid_blocked_def valid_blocked_except_def split: option.splits)
  apply (intro conjI impI)
             apply (force+)[8]
     apply (clarsimp simp: valid_blocked_except_def)
     apply (case_tac "t=target")
      apply (force simp: not_queued_def tcb_sched_enqueue_def split: if_split_asm)
     apply (erule_tac x=t in allE)
     apply (force simp: not_queued_def tcb_sched_enqueue_def split: if_split_asm)
    apply force
   apply (clarsimp simp: valid_blocked_except_def)
   apply (case_tac "t=target")
    apply (force simp: not_queued_def tcb_sched_enqueue_def split: if_split_asm)
   apply (erule_tac x=t in allE)
   apply (force simp: not_queued_def tcb_sched_enqueue_def split: if_split_asm)
  apply force
  done

lemma attempt_switch_to_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target and st_tcb_at runnable target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     attempt_switch_to target \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: attempt_switch_to_def | wp possible_switch_to_valid_sched')+

(* FIXME - Move *)
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
   apply (wp static_imp_wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a)
   apply (rule hoare_convert_imp)
    apply (rule typ_at_st_tcb_at_lift)
     apply (wp a t)+
  apply (simp add: valid_blocked_except_def)
  done

crunch valid_blocked_except[wp]: as_user "valid_blocked_except thread"
  (wp: valid_blocked_except_lift)


(* FIXME: Move *)

lemma set_notification_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps valid_sched_action_lift | simp add: set_notification_def)+

crunch not_cur_thread[wp]: cap_insert_ext "not_cur_thread t"

crunch not_cur_thread[wp]: cap_insert, set_extra_badge "not_cur_thread t"
  (wp: hoare_drop_imps)

lemma transfer_caps_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

crunch not_cur_thread[wp]: do_ipc_transfer, as_user "not_cur_thread t"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

lemma switch_if_required_to_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target and st_tcb_at runnable target and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     switch_if_required_to target \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: switch_if_required_to_def | wp possible_switch_to_valid_sched')+

lemmas set_thread_state_active_valid_sched_except_blocked =
  set_thread_state_runnable_valid_sched_except_blocked[simplified runnable_eq_active]

lemma set_thread_state_runnable_valid_blocked:
  "\<lbrace>valid_blocked and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wp gts_wp)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_def obj_at_def get_tcb_def)
  apply (case_tac "tcb_state y", simp_all)
  done

lemma set_thread_state_runnable_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp set_thread_state_runnable_valid_queues
                                        set_thread_state_runnable_valid_sched_action
                                        set_thread_state_runnable_valid_blocked)+
  done

context DetSchedSchedule_AI begin
lemma update_waiting_ntfn_valid_sched[wp]:
  "\<lbrace> \<lambda>s. valid_sched s \<and> hd queue \<noteq> idle_thread s \<and> (scheduler_action s = resume_cur_thread \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace> update_waiting_ntfn ntfnptr queue badge val \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (wp sts_st_tcb_at' switch_if_required_to_valid_sched'
            set_thread_state_runnable_valid_sched
            set_thread_state_runnable_valid_queues
            set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except 
            | clarsimp)+
  apply (clarsimp simp add: valid_sched_def not_cur_thread_def ct_not_in_q_def)
  done
end

crunch valid_sched[wp]: dec_domain_time valid_sched

lemma timer_tick_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> timer_tick \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: timer_tick_def crunch_simps thread_set_time_slice_def
                   trans_state_update'[symmetric] ethread_set_def set_eobject_def
           | wp gts_wp reschedule_required_valid_sched tcb_sched_action_append_valid_blocked
           | wpc | rule hoare_strengthen_post, rule dec_domain_time_valid_sched,
                                      simp add: valid_sched_def valid_sched_action_def)+
  by (fastforce simp: valid_sched_def valid_etcbs_def valid_queues_def pred_tcb_weakenE
         valid_sched_action_def weak_valid_sched_action_def etcb_at_def is_etcb_at_def
         get_etcb_def in_cur_domain_def ct_in_cur_domain_2_def switch_in_cur_domain_def
         valid_idle_etcb_2_def
         split: option.splits)

lemma cancel_badged_sends_filterM_valid_etcbs[wp]:
   "\<lbrace>valid_etcbs\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> (tcb_sched_action tcb_sched_enqueue t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply simp
  apply (clarsimp simp: filterM_append)
  apply (wp sts_st_tcb_at' | simp)+
  done

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

lemma cap_revoke_valid_sched':
  "\<lbrace>valid_sched and simple_sched_action and \<top>\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched and simple_sched_action\<rbrace>"
  by (wp cap_revoke_preservation_desc_of preemption_point_inv' | fastforce)+

lemma cap_revoke_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule cap_revoke_valid_sched')
   apply simp+
   done

lemma cap_revoke_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> cap_revoke slot \<lbrace>\<lambda>rv. simple_sched_action\<rbrace>"
  by (wp cap_revoke_preservation_desc_of preemption_point_inv' | fastforce)+

end

lemma thread_set_state_eq_valid_queues:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_queues and st_tcb_at (op = ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_valid_sched_action:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_sched_action and st_tcb_at (op = ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: valid_sched_action_def weak_valid_sched_action_def
                         is_activatable_def st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_ct_in_cur_domain:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>ct_in_cur_domain and st_tcb_at (op = ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: ct_in_cur_domain_def st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_valid_blocked:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_blocked and st_tcb_at (op = ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_def2)
  done

crunch etcb_at[wp]: thread_set "etcb_at P t"

context DetSchedSchedule_AI begin
lemma thread_set_state_eq_valid_sched:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_sched and st_tcb_at (op = ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wp thread_set_state_eq_valid_queues thread_set_state_eq_valid_blocked thread_set_state_eq_valid_sched_action thread_set_state_eq_ct_in_cur_domain | simp)+
  done
end

crunch exst[wp]: thread_set "\<lambda>s. P (exst s)"

lemma ethread_set_not_switch_switch_in_cur_domain:
  "\<lbrace>switch_in_cur_domain and (\<lambda>s. scheduler_action s \<noteq> switch_thread tptr)\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def is_etcb_at_def etcb_at_def get_etcb_def)
  done

lemma ethread_set_not_cur_ct_in_cur_domain:
  "\<lbrace>ct_in_cur_domain and not_cur_thread tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def not_cur_thread_def etcb_at_def get_etcb_def)
  done

lemma ethread_set_valid_blocked:
  "\<lbrace>valid_blocked\<rbrace> ethread_set f tptr \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  by (wp valid_blocked_lift | simp add: ethread_set_def set_eobject_def)+

lemma ethread_set_inactive_valid_idle_etcb:
  notes valid_idle_etcb_lift[wp del]
  shows
  "\<lbrace>valid_idle_etcb and valid_idle and st_tcb_at inactive tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  apply(simp add: ethread_set_def set_eobject_def)
  apply wp
  apply(clarsimp simp: get_etcb_def valid_idle_etcb_def etcb_at'_def valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma ethread_set_inactive_valid_sched:
  "\<lbrace>valid_sched and valid_idle and st_tcb_at inactive tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_sched_action_def | wp ethread_set_not_queued_valid_queues ethread_set_not_switch_switch_in_cur_domain ethread_set_not_cur_ct_in_cur_domain ethread_set_valid_blocked ethread_set_inactive_valid_idle_etcb)+
        apply (force simp: valid_idle_def st_tcb_at_def obj_at_def not_cur_thread_def
                           is_activatable_def weak_valid_sched_action_def valid_queues_def
                           not_queued_def)+
  done

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

crunch valid_sched[wp]: cap_move valid_sched

context DetSchedSchedule_AI begin
lemma invoke_cnode_valid_sched:
  "\<lbrace>valid_sched and invs and valid_cnode_inv a and simple_sched_action\<rbrace> invoke_cnode a \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply wpc
         apply (simp add: liftE_def | (wp hoare_vcg_all_lift)+ | wp_once hoare_drop_imps | wpc)+
  apply force
  done
end

crunch valid_sched[wp]: set_extra_badge valid_sched (wp: crunch_wps)

lemma transfer_caps_valid_sched:
  "\<lbrace>valid_sched\<rbrace> transfer_caps info caps ep recv recv_buf \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+
  done

context DetSchedSchedule_AI begin

crunch valid_sched[wp]: do_ipc_transfer, handle_fault_reply valid_sched
  (wp: crunch_wps)

lemma do_reply_transfer_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_objs and cte_wp_at (op = (ReplyCap t' False)) slot and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
     do_reply_transfer sender receiver slot
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp set_thread_state_not_runnable_valid_sched sts_st_tcb_at'
       cap_delete_one_reply_st_tcb_at do_ipc_transfer_non_null_cte_wp_at2 thread_set_not_state_valid_sched thread_set_no_change_tcb_state attempt_switch_to_valid_sched' | wpc | clarsimp split del: if_split)+
        apply (wp set_thread_state_runnable_valid_queues
                  set_thread_state_runnable_valid_sched_action
                  set_thread_state_valid_blocked_except sts_st_tcb_at')[1]
       apply (rule_tac Q="\<lambda>_. valid_sched and (\<lambda>s. receiver \<noteq> idle_thread s)" in hoare_strengthen_post)
        apply wp
       apply (simp add: valid_sched_def)
      apply (wp attempt_switch_to_valid_sched')+
           apply simp
           apply (rule conjI)
            apply clarsimp
            apply (rule_tac P="valid_sched and st_tcb_at (\<lambda>ts. \<not> runnable ts) receiver and (\<lambda>s. receiver \<noteq> idle_thread s)" in hoare_weaken_pre)
             apply (wp set_thread_state_runnable_valid_queues
                       set_thread_state_runnable_valid_sched_action
                       set_thread_state_valid_blocked_except sts_st_tcb_at')[1]
            apply (simp add: valid_sched_def)
           apply clarsimp
           apply (wp set_thread_state_not_runnable_valid_sched)
           apply simp
          apply (wp thread_set_not_state_valid_sched thread_set_no_change_tcb_state
                    cap_delete_one_reply_st_tcb_at | simp)+
    apply (wp hoare_drop_imps hoare_vcg_all_lift)[1]
   apply (simp add: get_thread_state_def thread_get_def | wp)+
  apply (fastforce simp: st_tcb_at_get_lift)
  done

end

lemma set_thread_state_not_queued_valid_queues:
  "\<lbrace>valid_queues and not_queued thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add: set_thread_state_ext_def set_object_def)+
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
   apply (wp gts_wp | simp add:  set_thread_state_ext_def set_object_def)+
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                         scheduler_act_not_def is_activatable_def pred_tcb_at_def
                         obj_at_def)
  apply (wp gts_wp | simp add: set_thread_state_ext_def set_object_def)+
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
     setup_caller_cap sender receiver
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: setup_caller_cap_def |
      wp set_thread_state_sched_act_not_valid_sched)+


(* strong in case of tcb_domain t = tcb_domain target *)
lemma possible_switch_to_sched_act_not[wp]:
  "\<lbrace>K(t \<noteq> target) and scheduler_act_not t\<rbrace>
     possible_switch_to target b
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def 
              split del: if_split 
        | wp | wpc)+
  apply (clarsimp simp: etcb_at_def scheduler_act_not_def split: option.splits)
  done


lemma possible_switch_to_not_queued:
  "\<lbrace>not_queued t and scheduler_act_not t and K(target \<noteq> t)\<rbrace>
     possible_switch_to target b
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def split del: if_split | wp | wpc)+
  by (fastforce simp: etcb_at_def tcb_sched_enqueue_def simple_sched_action_def
                         not_queued_def scheduler_act_not_def
                   split: option.splits)


crunch sched_act_not[wp]: attempt_switch_to, switch_if_required_to
  "scheduler_act_not t"

crunch not_queued[wp]: attempt_switch_to, switch_if_required_to
  "not_queued t"

lemma set_thread_state_ready_queues[wp]:
  "\<lbrace>\<lambda>s :: det_state. P (ready_queues s)\<rbrace>
    set_thread_state thread ts
   \<lbrace>\<lambda>r s. P (ready_queues s)\<rbrace>"
  apply (simp add: set_thread_state_def )
  apply (simp add: set_thread_state_ext_def[abs_def] reschedule_required_def
                   set_scheduler_action_def set_object_def)
  apply (wp | wpc | simp add: tcb_sched_action_def)+
  done

crunch scheduler_act[wp]: cap_insert_ext "\<lambda>s :: det_ext state. P (scheduler_action s)"
crunch scheduler_act[wp]: set_extra_badge,cap_insert "\<lambda>s :: det_state. P (scheduler_action s)" (wp: crunch_wps)

context DetSchedSchedule_AI begin

crunch scheduler_act[wp]: do_ipc_transfer "\<lambda>s :: det_state. P (scheduler_action s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

crunch ready_queues[wp]: cap_insert_ext "\<lambda>s :: det_ext state. P (ready_queues s)"

crunch ready_queues[wp]: cap_insert,set_extra_badge,do_ipc_transfer, set_endpoint, thread_set, setup_caller_cap "\<lambda>s :: det_state. P (ready_queues s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

end

crunch sched_act_not[wp]: set_thread_state_ext "scheduler_act_not t"
  (ignore: set_scheduler_action
   simp: set_scheduler_action_def if_fun_split scheduler_act_not_def
   wp: gts_wp)

crunch sched_act_not[wp]: set_thread_state, set_endpoint "scheduler_act_not t"
  (wp: hoare_drop_imps)

context DetSchedSchedule_AI begin
lemma send_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and scheduler_act_not thread and not_queued thread and invs\<rbrace>
   send_ipc block call badge can_grant thread epptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (wp set_thread_state_sched_act_not_valid_sched | wpc )+
            apply ((wp set_thread_state_sched_act_not_valid_sched
                       setup_caller_cap_sched_act_not_valid_sched
                       attempt_switch_to_valid_sched'
                       hoare_vcg_if_lift2 hoare_drop_imps | simp)+)[5]
       apply (wp set_thread_state_runnable_valid_queues
                 set_thread_state_runnable_valid_sched_action
                 set_thread_state_valid_blocked_except sts_st_tcb_at')
      apply simp
      apply (rule_tac Q="\<lambda>_. valid_sched and scheduler_act_not thread and not_queued thread and (\<lambda>s. x21 \<noteq> idle_thread s \<and> x21 \<noteq> thread)" in hoare_strengthen_post)
       apply ((wp|wpc)+)[1]
      apply (clarsimp simp: valid_sched_def)
     apply (simp | wp gts_wp hoare_vcg_all_lift)+
    apply (wp hoare_vcg_imp_lift)
     apply ((simp add: set_endpoint_def set_object_def | wp hoare_drop_imps | wpc)+)[1]
    apply (wp hoare_vcg_imp_lift get_object_wp | simp add: get_endpoint_def | wpc |
           wp_once hoare_vcg_all_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])
  apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def2 obj_at_def
                        valid_sched_def valid_sched_action_def weak_valid_sched_action_def)+
  apply (clarsimp simp: scheduler_act_not_def)
  apply (subgoal_tac "xb \<noteq> idle_thread s")
   apply fastforce
  apply clarsimp
  apply (frule invs_valid_idle)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done
end

crunch not_queued[wp]: thread_set "not_queued t"

crunch sched_act_not[wp]: thread_set "scheduler_act_not t"

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
    not_queued tptr and invs and (\<lambda>_. valid_fault fault)\<rbrace> send_fault_ipc tptr fault \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: send_fault_ipc_def Let_def)
  apply (wp send_ipc_valid_sched thread_set_not_state_valid_sched thread_set_no_change_tcb_state hoare_gen_asm'[OF thread_set_tcb_fault_set_invs]  hoare_drop_imps hoare_vcg_all_lift_R | wpc | simp)+
  done
end

crunch valid_sched[wp]: delete_caller_cap valid_sched

lemma handle_double_fault_valid_queues:
  "\<lbrace>valid_queues and not_queued tptr\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: handle_double_fault_def set_thread_state_def)
  apply (wp | simp add:  set_thread_state_ext_def set_object_def)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split not_queued_def)
  done

lemma handle_double_fault_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tptr\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: handle_double_fault_def set_thread_state_def)
  apply (wp gts_wp | simp add: set_thread_state_ext_def set_object_def)+
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
  apply (wp handle_double_fault_valid_queues handle_double_fault_valid_sched_action
            set_thread_state_not_runnable_valid_blocked
          | rule hoare_conjI | simp add: handle_double_fault_def | fastforce simp: simple_sched_action_def)+
  done

lemma send_fault_ipc_error_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv. scheduler_act_not t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_cur_thread[wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

lemma send_fault_ipc_error_not_queued[wp]:
  "\<lbrace>not_queued t\<rbrace> send_fault_ipc tptr fault -, \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

context DetSchedSchedule_AI begin
lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and not_queued thread and scheduler_act_not thread and invs and (\<lambda>_. valid_fault ex)\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: handle_fault_def | wp handle_double_fault_valid_sched send_fault_ipc_valid_sched)+
end

lemma idle_not_queued'':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s); queue \<times> {rt} \<subseteq> state_refs_of s ptr\<rbrakk> \<Longrightarrow> 
     idle_thread s \<notin> queue"
  by (frule idle_no_refs, fastforce simp: valid_idle_def sym_refs_def)

context DetSchedSchedule_AI begin

lemma send_signal_valid_sched[wp]:
  "\<lbrace> valid_sched and invs \<rbrace> send_signal ntfnptr badge \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: send_signal_def)
  apply (wp get_ntfn_wp switch_if_required_to_valid_sched'  
            set_thread_state_runnable_valid_queues set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except sts_st_tcb_at' gts_wp  | wpc | clarsimp)+
       apply (rename_tac ntfn a st)
       apply (rule_tac Q="\<lambda>rv s. valid_sched s \<and> a \<noteq> idle_thread s \<and> not_cur_thread a s" in hoare_strengthen_post)
        apply (wp gts_wp get_ntfn_wp | simp add: valid_sched_def)+
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

crunch valid_sched[wp]: handle_interrupt, complete_signal valid_sched
  (ignore: resetTimer ackInterrupt wp: gts_wp hoare_drop_imps
   simp: op_equal pred_tcb_weakenE hoare_if_r_and)

lemma receive_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and ct_active
          and not_queued thread and scheduler_act_not thread and invs\<rbrace>
   receive_ipc thread cap is_blocking
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: receive_ipc_def)
  including no_pre
  apply (wp | wpc | simp)+
        apply (wp set_thread_state_sched_act_not_valid_sched | wpc)+
                 apply ((wp set_thread_state_sched_act_not_valid_sched
                            setup_caller_cap_sched_act_not_valid_sched
                        | simp add: do_nbrecv_failed_transfer_def)+)[2]
               apply ((wp switch_if_required_to_valid_sched' sts_st_tcb_at' hoare_drop_imps
                          set_thread_state_runnable_valid_queues
                          set_thread_state_runnable_valid_sched_action
                          set_thread_state_valid_blocked_except | simp | wpc)+)[3]
             apply simp
             apply (rule_tac Q="\<lambda>_. valid_sched and scheduler_act_not (sender) and not_queued (sender) and not_cur_thread (sender) and (\<lambda>s. sender \<noteq> idle_thread s)" in hoare_strengthen_post)
              apply wp
             apply (simp add: valid_sched_def)
            apply ((wp | wpc)+)[1]
           apply (simp | wp gts_wp hoare_vcg_all_lift)+
          apply (wp hoare_vcg_imp_lift)
           apply ((simp add: set_endpoint_def set_object_def | 
                   wp hoare_drop_imps | wpc)+)[1]
          apply (wp hoare_vcg_imp_lift get_object_wp
                    set_thread_state_sched_act_not_valid_sched gbn_wp
               | simp add: get_endpoint_def get_notification_def do_nbrecv_failed_transfer_def
               | wpc
               | wp_once hoare_vcg_all_lift hoare_vcg_ex_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])+
  apply (clarsimp simp: st_tcb_at_kh_if_split default_notification_def default_ntfn_def isActive_def)
  apply (drule_tac t="hd xh" and P'="\<lambda>ts. \<not> active ts" in st_tcb_weakenE)
   apply clarsimp
  apply (simp only: st_tcb_at_not)
  apply (subgoal_tac "hd xh \<noteq> idle_thread s")
   apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def valid_queues_def st_tcb_at_not ct_in_state_def not_cur_thread_def runnable_eq_active not_queued_def scheduler_act_not_def split: scheduler_action.splits)
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
  done

end

crunch valid_sched: receive_signal valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched)

crunch cur_thread[wp]: delete_caller_cap "\<lambda>s. P (cur_thread s)"

crunch sched_act_not[wp]: delete_caller_cap "scheduler_act_not t"
  (simp: unless_def
   wp: hoare_drop_imps set_scheduler_action_wp mapM_x_wp
   ignore: set_scheduler_action)

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

crunch sched_act_not[wp]: tcb_sched_action "scheduler_act_not t"

crunch not_queued[wp]: set_thread_state "not_queued t"

context DetSchedSchedule_AI begin
lemma cancel_all_ipc_not_queued:
  "\<lbrace>st_tcb_at active t and valid_objs and not_queued t and scheduler_act_not t
        and sym_refs \<circ> state_refs_of\<rbrace>
     cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
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
    apply (wp hoare_vcg_imp_lift | simp add: get_ep_queue_def get_endpoint_def
              get_object_def | wpc | wp_once hoare_vcg_all_lift)+
   apply safe
   apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep="SendEP xa" in
          ep_queued_st_tcb_at[rotated, rotated])
       apply (simp_all only: st_tcb_at_not)
      apply (simp add: obj_at_def)+
  apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep="RecvEP xa" in ep_queued_st_tcb_at[rotated, rotated])
      apply (simp_all only: st_tcb_at_not)
     apply (fastforce simp: obj_at_def)+
  done
end

crunch not_queued[wp]: set_notification "not_queued t"
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
  apply (wp hoare_vcg_imp_lift | simp add: get_notification_def get_object_def |
         wpc | wp_once hoare_vcg_all_lift)+
   apply safe
  apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep=x in
         ntfn_queued_st_tcb_at[rotated, rotated])
  apply (simp_all only: st_tcb_at_not)
  apply (fastforce simp: obj_at_def)+
  done

lemma unbind_maybe_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_maybe_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  unfolding unbind_maybe_notification_def
  apply (wp thread_set_valid_objs_triv set_ntfn_valid_objs hoare_drop_imp get_ntfn_wp | wpc | simp add: tcb_cap_cases_def
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
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp])
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
   apply (frule_tac P="op = (Some a)" in ntfn_bound_tcb_at, simp_all add: obj_at_def)[1]
   apply (fastforce simp: ntfn_q_refs_no_NTFNBound obj_at_def is_tcb state_refs_of_def 
                          tcb_st_refs_of_no_NTFNBound tcb_bound_refs_def2 tcb_ntfn_is_bound_def 
                          tcb_st_refs_no_TCBBound
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (frule ko_at_state_refs_ofD, simp)
  done

crunch not_queued[wp]: unbind_maybe_notification, unbind_notification "not_queued t"

context DetSchedSchedule_AI begin

lemma fast_finalise_not_queued:
  "\<lbrace>not_queued t and (st_tcb_at active t and valid_objs and scheduler_act_not t and
    sym_refs \<circ> state_refs_of)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (cases cap, simp_all)
     apply (wp cancel_all_ipc_not_queued cancel_all_signals_not_queued
            get_ntfn_wp unbind_maybe_notification_valid_objs | simp)+
  done

crunch not_queued: delete_caller_cap "not_queued t"
  (wp: fast_finalise_not_queued hoare_drop_imps simp: if_fun_split unless_def)

end

lemma set_endpoint_ct_active:
  "\<lbrace>ct_active\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def | wp get_object_wp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
                  split: kernel_object.splits)
  done

crunch is_etcb_at[wp]: setup_reply_master "is_etcb_at t"
crunch valid_etcbs[wp]: setup_reply_master "valid_etcbs"
crunch weak_valid_sched_action[wp]: setup_reply_master "weak_valid_sched_action"

crunch is_etcb_at_ext[wp]: set_thread_state_ext, tcb_sched_action,
                           reschedule_required, empty_slot_ext "is_etcb_at t"

crunch is_etcb_at[wp]: set_thread_state, cancel_ipc "is_etcb_at t"
  (wp: hoare_drop_imps crunch_wps select_inv simp: crunch_simps unless_def)

lemma set_eobject_is_etcb_at_ext[wp]:
  "\<lbrace>is_etcb_at t\<rbrace> set_eobject ptr etcb \<lbrace>\<lambda>_. is_etcb_at t\<rbrace>"
  apply (simp add: set_eobject_def | wp)+
  apply (simp add: is_etcb_at_def split: if_split_asm)
  done

crunch is_etcb_at_ext[wp]: ethread_set "is_etcb_at t"

crunch valid_etcbs[wp]: set_mrs valid_etcbs
  (wp: valid_etcbs_lift)

lemma cap_insert_check_cap_ext_valid[wp]:"
  \<lbrace>valid_list\<rbrace>
   check_cap_at new_cap src_slot
    (check_cap_at t slot
      (cap_insert new_cap src_slot x))
   \<lbrace>\<lambda>rv. valid_list\<rbrace>"
   apply (simp add: check_cap_at_def)
   apply (wp get_cap_wp | simp)+
   done

lemma opt_update_thread_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace>
    option_update_thread t fn v
   \<lbrace>\<lambda>_. valid_list\<rbrace>"
   apply (rule hoare_pre)
   apply (simp add: option_update_thread_def)
   apply (wp | wpc | simp)+
   done

lemma opt_update_thread_valid_sched[wp]:
  "(\<And>x a. tcb_state (fn a x) = tcb_state x) \<Longrightarrow>
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

crunch ct_active[wp]: delete_caller_cap ct_active (wp: ct_in_state_thread_state_lift)

crunch valid_sched[wp]: lookup_cap valid_sched

lemma test:
"invs s \<longrightarrow> (\<exists>y. get_tcb thread s = Some y) \<longrightarrow> s \<turnstile> tcb_ctable (the (get_tcb thread s))"
apply (simp add: invs_valid_tcb_ctable_strengthen)
done

context DetSchedSchedule_AI begin

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active
      and ct_not_queued and scheduler_act_sane\<rbrace>
   handle_recv is_blocking \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
              cong: if_cong)
  apply (wp get_ntfn_wp handle_fault_valid_sched delete_caller_cap_not_queued receive_ipc_valid_sched receive_signal_valid_sched | simp)+
     apply (rule hoare_vcg_E_elim)
      apply (simp add: lookup_cap_def lookup_slot_for_thread_def)
      apply wp
       apply (simp add: split_def)
       apply (wp resolve_address_bits_valid_fault2)+
     apply (simp add: valid_fault_def)
     apply (wp hoare_drop_imps hoare_vcg_all_lift_R)
    apply (wp delete_caller_cap_not_queued | simp | strengthen invs_valid_tcb_ctable_strengthen)+
  apply (simp add: ct_in_state_def tcb_at_invs)
  apply (auto simp: objs_valid_tcb_ctable invs_valid_objs)
  done

lemma handle_recv_valid_sched':
  "\<lbrace>invs and valid_sched and ct_active and ct_not_queued and scheduler_act_sane\<rbrace>
    handle_recv is_blocking
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wp handle_recv_valid_sched)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  done

end

crunch valid_sched[wp]: reply_from_kernel valid_sched

crunch etcb_at[wp]: cap_insert "\<lambda>s. etcb_at P t s"
  (wp: crunch_wps simp: cap_insert_ext_def)

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
crunch valid_sched[wp]: invoke_irq_control, invoke_irq_handler "valid_sched"
end

lemma simple_sched_action_sched_act_not[simp]:
  "simple_sched_action s \<Longrightarrow> scheduler_act_not t s"
  by (fastforce simp: simple_sched_action_def scheduler_act_not_def)

declare valid_idle_etcb_lift[wp del]

lemma ethread_set_not_activatable_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb and valid_idle and st_tcb_at (\<lambda>ts. \<not> activatable ts) tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  apply(simp add: ethread_set_def set_eobject_def)
  apply wp
  apply(clarsimp simp: get_etcb_def valid_idle_etcb_def etcb_at'_def valid_idle_def pred_tcb_at_def obj_at_def)
  done


lemma ethread_set_not_activatable_valid_sched:
  "\<lbrace>valid_sched and valid_idle and st_tcb_at (\<lambda>ts. \<not> activatable ts) tptr\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_sched_action_def | wp ethread_set_not_queued_valid_queues ethread_set_not_switch_switch_in_cur_domain ethread_set_not_cur_ct_in_cur_domain ethread_set_valid_blocked ethread_set_not_activatable_valid_idle_etcb)+
        apply (force simp: valid_idle_def st_tcb_at_def obj_at_def not_cur_thread_def
                           is_activatable_def weak_valid_sched_action_def valid_queues_def
                           not_queued_def split: thread_state.splits)+
  done

lemma ethread_set_not_idle_valid_idle_etcb:
  "\<lbrace>valid_idle_etcb and valid_idle and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_idle_etcb\<rbrace>"
  apply(simp add: ethread_set_def set_eobject_def)
  apply wp
  apply(clarsimp simp: get_etcb_def valid_idle_etcb_def etcb_at'_def valid_idle_def st_tcb_at_def obj_at_def)
  done
  
lemma ethread_set_not_idle_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action and not_queued tptr and (\<lambda>s. tptr \<noteq> cur_thread s) and (\<lambda>s. tptr \<noteq> idle_thread s) and valid_idle\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def valid_sched_action_def | wp ethread_set_not_queued_valid_queues ethread_set_not_switch_switch_in_cur_domain ethread_set_not_cur_ct_in_cur_domain ethread_set_valid_blocked ethread_set_not_idle_valid_idle_etcb)+
        apply (force simp: simple_sched_action_def st_tcb_at_def obj_at_def not_cur_thread_def
                           is_activatable_def weak_valid_sched_action_def valid_queues_def
                           not_queued_def split: thread_state.splits)+
  done

lemma ethread_set_ssa_valid_sched_action:
  "\<lbrace>valid_sched_action and simple_sched_action\<rbrace>
     ethread_set f tptr \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def | wp ethread_set_not_switch_switch_in_cur_domain)+
    apply (force simp: simple_sched_action_def)+
    done

lemma ethread_set_valid_blocked_except:
  "\<lbrace>valid_blocked_except t\<rbrace> ethread_set f tptr \<lbrace>\<lambda>_. valid_blocked_except t\<rbrace>"
  by (wp valid_blocked_except_lift | simp add: ethread_set_def set_eobject_def)+

declare tcb_sched_action_valid_idle_etcb[wp]

lemma invoke_domain_valid_sched[wp]:
  "\<lbrace>valid_sched and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s)
                and simple_sched_action and valid_idle\<rbrace>
    invoke_domain t d \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: invoke_domain_def)
  including no_pre
  apply wp
  apply (simp add: set_domain_def thread_set_domain_def)
  apply (wp gts_st_tcb_at hoare_vcg_if_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift 
            hoare_vcg_disj_lift ethread_set_not_queued_valid_queues reschedule_required_valid_sched
            tcb_sched_action_enqueue_valid_blocked ethread_set_valid_blocked_except
            ethread_set_valid_blocked ethread_set_ssa_valid_sched_action
            ethread_set_not_cur_ct_in_cur_domain ethread_set_not_idle_valid_sched
            ethread_set_not_idle_valid_idle_etcb)
     apply(wp static_imp_wp static_imp_conj_wp tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except)
    apply simp
    apply (wp hoare_vcg_disj_lift)
    apply (rule_tac Q="\<lambda>_. valid_sched and not_queued t and valid_idle and (\<lambda>s. t \<noteq> idle_thread s)" in hoare_strengthen_post)
     apply (wp tcb_sched_action_dequeue_valid_sched_not_runnable tcb_dequeue_not_queued)
    apply (simp add: valid_sched_def valid_sched_action_def)
   apply simp
   apply (wp hoare_vcg_disj_lift tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except
             tcb_sched_action_dequeue_valid_sched_not_runnable)+
   apply (clarsimp simp: valid_sched_def not_cur_thread_def valid_sched_action_def not_pred_tcb)
   apply (force simp: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: valid_sched_def not_cur_thread_def valid_sched_action_def not_pred_tcb)
  apply (force simp: pred_tcb_at_def obj_at_def)
  done

lemma idle_not_reply_cap:
  "\<lbrakk> valid_idle s; valid_reply_caps s; cte_wp_at (op = (ReplyCap r False)) p s \<rbrakk> \<Longrightarrow> r \<noteq> idle_thread s"
  apply (drule_tac p=p in valid_reply_caps_of_stateD)
   apply (simp add: caps_of_state_def cte_wp_at_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

context DetSchedSchedule_AI begin
lemma perform_invocation_valid_sched[wp]:
  "\<lbrace>invs and valid_invocation i and ct_active and simple_sched_action and valid_sched
         and (\<lambda>s. not_queued (cur_thread s) s)\<rbrace>
     perform_invocation calling blocking i
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases i, simp_all)
          apply (wp invoke_untyped_valid_sched send_ipc_valid_sched | clarsimp)+
         apply (clarsimp simp: ct_in_state_def)
        apply (wp invoke_cnode_valid_sched send_ipc_valid_sched invoke_domain_valid_sched
             | simp add: invs_valid_objs idle_not_reply_cap invs_valid_idle invs_valid_reply_caps
             | clarsimp simp: ct_in_state_def)+
  done
end

crunch not_queued[wp]: set_thread_state_ext "not_queued t"

crunch ct_not_queued[wp]: set_thread_state ct_not_queued (wp: ct_not_queued_lift)

crunch valid_sched[wp]: lookup_cap_and_slot valid_sched

context DetSchedSchedule_AI begin
lemma handle_invocation_valid_sched:
  "\<lbrace>invs and valid_sched and ct_active and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     handle_invocation a b
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid handle_fault_valid_sched | wpc)+
                apply (wp set_thread_state_runnable_valid_sched)[1]
               apply wp+
         apply (wp gts_wp hoare_vcg_all_lift)
        apply (rule_tac Q="\<lambda>_. valid_sched" and E="\<lambda>_. valid_sched" in hoare_post_impErr)
          apply wp
         apply ((clarsimp simp: st_tcb_at_def obj_at_def)+)[2]
       apply (wp ct_in_state_set set_thread_state_runnable_valid_sched
             | simp add: split_def if_apply_def2 split del: if_split)+
      apply (simp add: validE_E_def)
      apply (rule hoare_post_impErr)
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
  "\<lbrace>valid_sched and ct_active and invs\<rbrace> handle_reply \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: handle_reply_def)
  apply (wp get_cap_wp | wpc | clarsimp)+
  apply (auto simp: invs_valid_objs idle_not_reply_cap invs_valid_idle invs_valid_reply_caps)
  done
end

crunch ct_not_queued[wp]: do_machine_op, cap_insert, set_extra_badge "\<lambda>s. not_queued (cur_thread s) s"
  (wp: hoare_drop_imps)

lemma transfer_caps_ct_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
     transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

crunch ct_sched_act_not[wp]: set_thread_state "\<lambda>s. scheduler_act_not (cur_thread s) s" (wp: set_scheduler_action_wp gts_wp
   simp: crunch_simps
   ignore: set_scheduler_action)

context DetSchedSchedule_AI begin

crunch not_queued[wp]: handle_fault_reply "not_queued t"

crunch sched_act_not[wp]: handle_fault_reply "scheduler_act_not t"

crunch valid_etcbs[wp]: set_extra_badge, do_ipc_transfer valid_etcbs
  (wp: transfer_caps_loop_pres crunch_wps const_on_failure_wp simp: crunch_simps)

crunch cur[wp]: handle_fault_reply "cur_tcb :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: cur_tcb_def unless_def)

end

crunch weak_valid_sched_action[wp]: empty_slot_ext, cap_delete_one weak_valid_sched_action
  (wp: crunch_wps set_thread_state_runnable_weak_valid_sched_action
       set_bound_notification_weak_valid_sched_action 
   simp: cur_tcb_def unless_def)

context DetSchedSchedule_AI begin

lemma do_reply_transfer_not_queued[wp]:
  "\<lbrace>not_queued t and invs and st_tcb_at active t and scheduler_act_not t and
    K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver slot
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp cap_delete_one_not_queued hoare_vcg_if_lift | wpc |
         clarsimp split del: if_split | wp_once hoare_drop_imps)+
   apply (simp add: invs_def valid_state_def valid_pspace_def)+ 
  done

lemma do_reply_transfer_schedact_not[wp]:
  "\<lbrace>scheduler_act_not t and K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver slot
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc | clarsimp split del: if_split |
         wp_once hoare_drop_imps)+
  done

end

lemma assert_false:"\<lbrace>\<lambda>s. \<not> P\<rbrace> assert P \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply wp
  apply simp
  done

lemma do_reply_transfer_add_assert:
  assumes a: "\<lbrace>st_tcb_at awaiting_reply receiver and P\<rbrace>
               do_reply_transfer sender receiver slot
              \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> do_reply_transfer sender receiver slot \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "st_tcb_at awaiting_reply receiver s")
   apply (rule hoare_pre)
    apply (wp a)
   apply simp
  apply (simp add: do_reply_transfer_def)
  apply (rule hoare_seq_ext)
   apply (rule hoare_seq_ext)
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
     do_reply_transfer sender receiver slot
   \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (rule do_reply_transfer_add_assert)
  apply (rule hoare_pre)
   apply (wp ct_not_queued_lift)
  apply (clarsimp simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma do_reply_transfer_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane and ct_active\<rbrace>
     do_reply_transfer sender receiver slot
   \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (rule do_reply_transfer_add_assert)
  apply (rule hoare_pre)
   apply (wp sch_act_sane_lift)
  apply (clarsimp simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

crunch ct_not_queued[wp]: handle_reply "ct_not_queued"
crunch scheduler_act_sane[wp]: handle_reply "scheduler_act_sane"

end

locale DetSchedSchedule_AI_handle_hypervisor_fault = DetSchedSchedule_AI +
  assumes handle_hyp_fault_valid_sched[wp]:
    "\<And>t fault.
      \<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t\<rbrace>
        handle_hypervisor_fault t fault
      \<lbrace>\<lambda>_. valid_sched\<rbrace>"

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_event_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def handle_call_def)
            apply ((rule hoare_pre, wp handle_invocation_valid_sched handle_recv_valid_sched'
              handle_reply_valid_sched 
              | fastforce simp: invs_valid_objs invs_sym_refs valid_sched_ct_not_queued)+)[5]
       apply (wp handle_fault_valid_sched hvmf_active hoare_drop_imps hoare_vcg_disj_lift
                 handle_recv_valid_sched' handle_reply_valid_sched |
              wpc |
              clarsimp simp: ct_in_state_def valid_sched_ct_not_queued |
              fastforce simp: valid_fault_def)+
  done

crunch valid_list[wp]: activate_thread valid_list
crunch valid_list[wp]: guarded_switch_to, switch_to_idle_thread, choose_thread valid_list
  (wp: crunch_wps)

end

crunch valid_list[wp]: next_domain valid_list (simp: Let_def)

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma schedule_valid_list[wp]: "\<lbrace>valid_list\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: Schedule_A.schedule_def)
  apply (wp tcb_sched_action_valid_list alternative_wp select_wp gts_wp | wpc | simp)+
  done

lemma call_kernel_valid_list[wp]: "\<lbrace>valid_list\<rbrace> call_kernel e \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: call_kernel_def)
  by (wp | simp)+

lemma call_kernel_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_active or ct_idle)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     call_kernel e
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp schedule_valid_sched activate_thread_valid_sched | simp)+
    apply (rule_tac Q="\<lambda>rv. invs" in hoare_strengthen_post)
     apply wp
    apply (erule invs_valid_idle)
   apply (wp hoare_vcg_if_lift2 hoare_drop_imps | simp)+
  apply (rule_tac Q="\<lambda>rv. valid_sched and invs" and
                  E="\<lambda>rv. valid_sched and invs" in hoare_post_impErr)
    apply (rule valid_validE)
    apply (wp handle_event_valid_sched)
     apply (force intro: active_from_running)+
  done

end

end
