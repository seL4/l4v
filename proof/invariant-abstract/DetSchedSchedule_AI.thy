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

crunch ct_not_in_q[wp]: do_machine_op "ct_not_in_q"

context begin interpretation Arch .
requalify_facts
  set_object_ct
end

declare set_object_ct[wp]

lemma ct_assumptions: "\<not>in_release_queue (cur_thread s) s
                       \<and> bound_sc_tcb_at (\<lambda>sc. sc = Some (cur_sc s)) (cur_thread s) s"
  sorry


lemma is_schedulable_sp:
  "\<lbrace>P\<rbrace> is_schedulable tp b \<lbrace>\<lambda>rv. (\<lambda>s. rv = the (is_schedulable_opt tp b s)) and P\<rbrace>"
  apply (clarsimp simp: is_schedulable_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp simp: hoare_vcg_if_lift2 obj_at_def is_tcb wp: get_sched_context_wp)
  apply(rule conjI)
   apply (clarsimp simp: Option.is_none_def is_schedulable_opt_def get_tcb_def)
  by (clarsimp simp: is_schedulable_opt_def get_tcb_def test_sc_refill_max_def split: option.splits)

lemma schedulable_unfold: "tcb_at tp s \<Longrightarrow> (the (is_schedulable_opt tp b s))
  = (st_tcb_at runnable tp s \<and>
     bound_sc_tcb_at (\<lambda>spo. \<exists>sp. spo = Some sp \<and> test_sc_refill_max sp s) tp s \<and> \<not>b)"
  by (clarsimp simp: is_schedulable_opt_def get_tcb_rev is_tcb pred_tcb_at_def obj_at_def split: option.splits)

lemma in_q_not_schedualble[simp]: "tcb_at tp s \<Longrightarrow> is_schedulable_opt tp True s = (Some False)"
  by (clarsimp simp: is_schedulable_opt_def get_tcb_ko_at obj_at_def is_tcb split: option.splits)

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

crunch valid_etcbs[wp]: tcb_sched_action "valid_etcbs"

lemma enqueue_distinct[intro!]: "distinct queue \<Longrightarrow> distinct (tcb_sched_enqueue thread queue)"
  apply (simp add: tcb_sched_enqueue_def)
  done

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 resume_cur_thread ekh kh rq"
  "weak_valid_sched_action_2 choose_new_thread ekh kh rq"
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
  "valid_sched_action_2 choose_new_thread ekh kh ct cdom rq"
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
  "valid_sched_except_blocked_2 queues ekh sa cdom kh ct it rq \<equiv>
      valid_etcbs_2 ekh kh \<and> valid_queues_2 queues ekh kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_2 sa ekh kh ct cdom rq \<and> ct_in_cur_domain_2 ct it sa cdom ekh \<and> valid_idle_etcb_2 ekh"

abbreviation valid_sched_except_blocked :: "det_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked s \<equiv> valid_sched_except_blocked_2 (ready_queues s) (ekheap s) (scheduler_action s) (cur_domain s) (kheap s) (cur_thread s) (idle_thread s) (release_queue s)"

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
  "\<lbrace>valid_queues\<rbrace>
      reschedule_required
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (wpsimp simp: reschedule_required_def is_schedulable_def
     wp: get_sched_context_wp)
  by (clarsimp simp: pred_tcb_at_def)

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

crunch valid_blocked[wp]: is_schedulable "valid_blocked"
crunch valid_blocked_except[wp]: is_schedulable "valid_blocked_except t"

lemma reschedule_required_valid_blocked:
  "\<lbrace>valid_blocked and weak_valid_sched_action\<rbrace> reschedule_required \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc)
    defer 2
    apply ((wpsimp wp: set_scheduler_action_cnt_valid_blocked)+)[2]
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (wpsimp wp: set_scheduler_action_cnt_valid_blocked tcb_sched_action_enqueue_valid_blocked)
   apply (simp add: tcb_sched_action_def)
   apply wp+
  apply clarsimp
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: valid_blocked_def valid_blocked_except_def etcb_at_def split: option.splits)
   apply (rename_tac tcb)
   apply (rule_tac x="tcb_domain tcb" in exI)
   apply (rule_tac x="tcb_priority tcb" in exI)
   apply (clarsimp simp: tcb_sched_enqueue_def)
  by (clarsimp simp: weak_valid_sched_action_def is_schedulable_opt_def pred_tcb_at_def obj_at_def
                     get_tcb_def schedulable_tcb_at_def test_sc_refill_max_def in_release_queue_def)

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
(*
lemma schedulable_tcb_at_kh_if_split:
  "schedulable_tcb_at_kh ptr (\<lambda>t. if t = ref then x else kh t)
     = (if ptr = ref then (\<exists>tcb. x = Some (TCB tcb) \<and> ((\<lambda>ko. \<exists>scp. ko = Some scp
                 \<and> (\<exists>sc n. kh scp = Some (SchedContext sc n)
                                    \<and> sc_refill_max sc > 0)) (tcb_sched_context tcb)))
        else schedulable_tcb_at_kh ptr kh)"
  apply (clarsimp simp: schedulable_tcb_at_kh_def bound_sc_tcb_at_kh_def obj_at_kh_def obj_at_def)
  apply (intro conjI impI iffI; clarsimp; rule_tac x=scp in exI; clarsimp)
  done
*)
lemma schedule_tcb_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> schedule_tcb ref \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: schedule_tcb_def)
  apply (wp | wpc | simp add: set_object_def)+
  done

lemma set_thread_state_ext_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_thread_state_ext ref \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: set_thread_state_ext_def)
  apply (wp | wpc | simp add: set_object_def)+
  done

lemma set_thread_state_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_if_split
                   dest: get_tcb_st_tcb_at)
  done

lemma set_bound_notification_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_if_split
                   dest: get_tcb_st_tcb_at)
  done

crunch valid_queues[wp]: schedule_tcb,set_thread_state_ext "valid_queues"
  (simp: unless_def is_schedulable_def wp: get_sched_context_wp hoare_vcg_if_lift2)

lemma set_thread_state_runnable_valid_queues:
  "\<lbrace>valid_queues and K (runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def)
  apply (wpsimp wp:  get_sched_context_wp hoare_drop_imp
         simp: is_schedulable_def set_object_def)
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split pred_tcb_at_def)
  done

lemma set_bound_notification_valid_queues:
  "\<lbrace>valid_queues\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp | wpc | simp add: set_object_def)+
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2)
  done

lemma schedule_tcb_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> schedule_tcb ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: schedule_tcb_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_ext_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state_ext ref \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: set_thread_state_ext_def is_schedulable_def wp: get_sched_context_wp)

lemma set_thread_state_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp gts_wp)+
  done

lemma set_bound_notification_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  done

lemma set_thread_state_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_thread_state ref ts
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def set_object_def is_schedulable_def
      split_del: if_split
      wp: set_scheduler_action_wp gts_wp hoare_vcg_if_lift2 get_sched_context_wp)
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def
              dest!: get_tcb_SomeD)
  done

lemma set_bound_notification_cur_is_activatable[wp]:
  "\<lbrace>\<lambda>s. is_activatable (cur_thread s) s\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update ref ntfn
   \<lbrace>\<lambda>_ (s::det_state). is_activatable (cur_thread s) s\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp)+
  apply (clarsimp simp: is_activatable_def st_tcb_at_kh_if_split pred_tcb_at_def
                        obj_at_def get_tcb_def)
  done

lemma set_thread_state_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. runnable ts)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def set_object_def
                wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split)
  apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
  by (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def; rule_tac x=scp in exI, clarsimp)

lemma set_thread_state_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp set_scheduler_action_wp)
  done

lemma set_bound_notification_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update ref ts \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp set_scheduler_action_wp gbn_wp)+
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
  apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
  by (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def get_tcb_rev;
      rule_tac x=scp in exI, clarsimp)

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
  apply (wpsimp simp: set_thread_state_ext_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp set_scheduler_action_wp)
  done

lemma set_bound_notification_cur_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update ref ts \<lbrace>\<lambda>_. ct_in_cur_domain\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def |
        wp set_scheduler_action_wp gbn_wp)+
  done

lemma set_thread_state_etcb_at[wp]: "\<lbrace>etcb_at P t\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. etcb_at P t\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def set_object_def
              wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  done

crunch etcb_at[wp]: set_tcb_obj_ref, get_tcb_obj_ref "etcb_at P t"

lemma set_thread_state_runnable_valid_sched_except_blocked:
  "\<lbrace>valid_sched and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched_except_blocked\<rbrace>"
  apply (simp add: valid_sched_def | wp set_thread_state_runnable_valid_queues
                                        set_thread_state_runnable_valid_sched_action)+
  done

lemma set_bound_notification_valid_sched_action:
  "\<lbrace>valid_sched_action\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_bound_notification_weak_valid_sched_action)+
  done

lemma set_bound_notification_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (simp add: set_object_def | wp)+
  apply (clarsimp simp: valid_blocked_def)
  apply (drule_tac x=ta in spec, clarsimp)
  apply (drule_tac x=st in spec)
  apply (simp only: st_tcb_at_kh_if_split)
  apply (simp add: st_tcb_def2 split: if_split_asm)
  done

crunch valid_blocked[wp]: get_tcb_obj_ref "valid_blocked"

lemma set_bound_notification_valid_sched:
  "\<lbrace>valid_sched\<rbrace> set_tcb_obj_ref tcb_bound_notification_update ref ntfn \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp set_bound_notification_valid_queues
                                        set_bound_notification_valid_sched_action)+
  done

lemma valid_blocked_valid_blocked_except[simp]:
  "valid_blocked s \<Longrightarrow> valid_blocked_except t s"
  by (simp add: valid_blocked_def valid_blocked_except_def)

lemma set_thread_state_valid_blocked_except:
  "\<lbrace>valid_blocked (*and simple_sched_action*)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked_except ref\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])

  apply (simp add: set_object_def | wp)+
     apply (clarsimp simp: set_thread_state_ext_def)
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp
                   split_del: if_split)
(*
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
defer
    apply (wpsimp wp: hoare_vcg_if_lift2 gts_wp split_del: if_split)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def get_tcb_rev)
  apply (case_tac "tcb_state y"; clarsimp)


  apply (wpsimp simp: set_thread_state_ext_def)
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wpsimp wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp set_object_wp simp: obj_at_def is_tcb)+
apply (clarsimp simp: valid_blocked_def valid_blocked_except_def)
apply (rule conjI; clarsimp)
apply (drule_tac x=t in spec)
apply (clarsimp simp: st_tcb_at_kh_def obj_at_kh_def obj_at_def split: if_split_asm)
apply (drule_tac x=ts in spec)
apply (clarsimp simp: pred_tcb_at_def obj_at_def)
*)

  sorry

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

lemma as_user_weak_valid_sched_action[wp]:
  "\<lbrace>weak_valid_sched_action\<rbrace> as_user ptr s \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: as_user_def set_object_def | wpc | wp)+
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
  by (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def get_tcb_rev;
      rule_tac x=scp in exI, clarsimp)

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
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
  by (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def get_tcb_rev;
      rule_tac x=scp in exI, clarsimp)

crunch ct_in_cur_domain[wp]: as_user ct_in_cur_domain
  (wp: ct_in_cur_domain_lift)

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
  assumes make_arch_fault_msg_ct_not_queued[wp]:
    "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
      make_arch_fault_msg ft t
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
  assumes handle_arch_fault_reply_ct_not_queued'[wp]:
    "\<And>f t x y. \<lbrace>ct_not_queued\<rbrace> handle_arch_fault_reply f t x y \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
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
  assumes make_fault_arch_msg_not_cur_thread[wp] :
    "\<And>ft t t'. make_arch_fault_msg ft t \<lbrace>not_cur_thread t'\<rbrace>"
  assumes make_fault_arch_msg_valid_sched[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_sched\<rbrace>"
  assumes make_fault_arch_msg_scheduler_action[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  assumes make_fault_arch_msg_ready_queues[wp] :
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  assumes make_fault_arch_msg_valid_etcbs[wp] :
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_etcbs\<rbrace>"
  assumes arch_get_sanitise_register_info_not_cur_thread[wp] :
    "\<And>ft t'. arch_get_sanitise_register_info ft \<lbrace>not_cur_thread t'\<rbrace>"
  assumes arch_get_sanitise_register_info_ct_not_queued[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>ct_not_queued\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_sched[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_sched\<rbrace>"
  assumes arch_get_sanitise_register_info_scheduler_action[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  assumes arch_get_sanitise_register_info_ready_queues[wp] :
    "\<And>P ft. arch_get_sanitise_register_info ft \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_etcbs[wp] :
    "\<And>ft. arch_get_sanitise_register_info ft \<lbrace>valid_etcbs\<rbrace>"
  assumes arch_get_sanitise_register_info_cur'[wp]:
    "\<And>f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_get_sanitise_register_info f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_post_modify_registers_not_cur_thread[wp] :
    "\<And>c ft t'. arch_post_modify_registers c ft \<lbrace>not_cur_thread t'\<rbrace>"
  assumes arch_post_modify_registers_valid_sched[wp] :
    "\<And>c ft. arch_post_modify_registers c ft \<lbrace>valid_sched\<rbrace>"
  assumes arch_post_modify_registers_scheduler_action[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  assumes arch_post_modify_registers_ready_queues[wp] :
    "\<And>P c ft. arch_post_modify_registers c ft \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  assumes arch_post_modify_registers_valid_etcbs[wp] :
    "\<And>c ft. arch_post_modify_registers c ft \<lbrace>valid_etcbs\<rbrace>"
  assumes arch_post_modify_registers_cur'[wp]:
    "\<And>c f. \<lbrace>cur_tcb :: det_ext state \<Rightarrow> bool\<rbrace> arch_post_modify_registers c f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  assumes arch_post_modify_registers_not_idle_thread[wp]:
    "\<And>c t. \<lbrace>\<lambda>s::det_ext state. t \<noteq> idle_thread s\<rbrace> arch_post_modify_registers c t \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  assumes arch_post_cap_deletion_valid_etcbs[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_etcbs\<rbrace>"
  assumes arch_post_cap_deletion_valid_sched[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>valid_sched\<rbrace>"
  assumes arch_post_cap_deletion_ct_not_in_q[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>ct_not_in_q\<rbrace>"
  assumes arch_post_cap_deletion_simple_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>simple_sched_action\<rbrace>"
  assumes arch_post_cap_deletion_not_cur_thread[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_cur_thread t\<rbrace>"
  assumes arch_post_cap_deletion_sched_act_not[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>scheduler_act_not t\<rbrace>"
  assumes arch_post_cap_deletion_not_queued[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>not_queued t\<rbrace>"
  assumes arch_post_cap_deletion_is_etcb_at[wp] :
    "\<And>c t. arch_post_cap_deletion c \<lbrace>is_etcb_at t\<rbrace>"
  assumes arch_post_cap_deletion_weak_valid_sched_action[wp] :
    "\<And>c. arch_post_cap_deletion c \<lbrace>weak_valid_sched_action\<rbrace>"


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
   \<lbrace>\<lambda>r s. valid_sched_action_2 (scheduler_action s) (ekheap s) (kheap s) thread (cur_domain s) (release_queue s)\<rbrace>"
  apply (simp add: tcb_sched_action_def unless_def set_tcb_queue_def)
  apply wp
  apply (clarsimp simp: etcb_at_def valid_sched_action_def split: option.split)
  done

context DetSchedSchedule_AI begin

lemma as_user_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> as_user tptr f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply wpsimp
  apply (clarsimp simp: valid_sched_def valid_etcbs_def valid_queues_def valid_sched_action_def
      st_tcb_at_kh_if_split st_tcb_def2 valid_blocked_def is_activatable_def
      split del: if_split cong: imp_cong conj_cong)
  apply (intro conjI impI; clarsimp?)
      apply (drule_tac x=tptr in spec, clarsimp simp: get_tcb_rev)
     apply (drule_tac x=d and y=p in spec2, clarsimp)
     apply (drule_tac x=tptr in bspec, clarsimp, clarsimp dest!: get_tcb_SomeD)
    apply (clarsimp dest!: get_tcb_SomeD)
   apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
   apply (rule conjI)
    apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
   apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
   apply (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def get_tcb_rev;
      rule_tac x=scp in exI, clarsimp)
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
   apply (rule arch_switch_to_thread_valid_queues')
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
  by (wpsimp wp: get_sched_context_wp
      simp: guarded_switch_to_def is_schedulable_def get_thread_state_def thread_get_def)

lemma tcb_sched_action_lift:
  "(\<And>f s. P s \<Longrightarrow> P (ready_queues_update f s))
  \<Longrightarrow> \<lbrace>P\<rbrace> tcb_sched_action a b \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp | simp add: tcb_sched_action_def etcb_at_def)+

lemma next_domain_valid_idle[wp]:
  "\<lbrace> valid_idle \<rbrace> next_domain \<lbrace> \<lambda>_. valid_idle \<rbrace>"
  apply (wpsimp simp: next_domain_def)
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

lemma next_domain_ct_in_q: "\<lbrace>ct_in_q\<rbrace> next_domain \<lbrace>\<lambda>_. ct_in_q\<rbrace>"
  apply (clarsimp simp: next_domain_def)
  apply (clarsimp simp: Let_def ct_in_q_def weak_valid_sched_action_def
                        get_etcb_def etcb_at_def)
  done

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

lemma set_sched_action_cnt_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action choose_new_thread \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  apply (simp add: set_scheduler_action_def | wp | wpc)+
  apply (simp add: not_cur_thread_def)
  done

lemma reschedule_required_not_cur_thread[wp]:
  "\<lbrace>\<top>\<rbrace> reschedule_required \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: reschedule_required_def | wp)+

lemma set_scheduler_action_switch_ct_not_in_q[wp]:
  "\<lbrace>\<top>\<rbrace> set_scheduler_action (switch_thread t) \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply (simp add: ct_not_in_q_def)
  done

lemma possible_switch_to_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q and (\<lambda>s. t \<noteq> cur_thread s)\<rbrace> possible_switch_to t \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  apply (simp add: possible_switch_to_def ethread_get_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp simp: not_cur_thread_def)
  done

crunch ct_not_in_q[wp]: update_sched_context,set_sc_obj_ref,set_tcb_obj_ref ct_not_in_q
crunch ct_not_in_q[wp]: tcb_release_remove ct_not_in_q
crunch ct_not_in_q[wp]: test_reschedule ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_vcg_if_lift2)

lemma sched_context_donate_ct_not_in_q[wp]:
  "\<lbrace>ct_not_in_q\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. ct_not_in_q\<rbrace>"
  by (wpsimp simp: sched_context_donate_def)

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
  apply (wpsimp wp: hoare_drop_imp)
  done

lemma update_sched_context_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_etcbs_def st_tcb_at_kh_if_split)
  apply (clarsimp simp: st_tcb_def2)
  apply (drule_tac x=ref in spec)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

lemma update_sched_context_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_queues_def st_tcb_at_kh_if_split)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp simp: st_tcb_def2 obj_at_def dest!: get_tcb_SomeD )
  done

lemma update_sched_context_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
      update_sched_context ref f
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: weak_valid_sched_action_def dest!: get_tcb_SomeD)
  apply (rule conjI)
   apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def obj_at_def get_tcb_rev)
  apply (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def bound_sc_tcb_at_kh_if_split)
  apply (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def obj_at_kh_def get_tcb_rev;
      rule_tac x=scp in exI, clarsimp)
  done

lemma update_sched_context_switch_in_cur_domain[wp]:
  "\<lbrace>switch_in_cur_domain\<rbrace>
      update_sched_context ref f \<lbrace>\<lambda>_. switch_in_cur_domain\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
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

lemma update_sched_context_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp update_sched_context_weak_valid_sched_action)+
  done

lemma update_sched_context_ct_in_cur_domain[wp]:
  "\<lbrace>ct_in_cur_domain\<rbrace>
     update_sched_context ptr f
   \<lbrace>\<lambda>_ . ct_in_cur_domain\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp set_scheduler_action_wp)
  done

lemma update_sched_context_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> update_sched_context ptr f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_blocked_def)
  apply (simp only: st_tcb_at_kh_if_split)
  apply (simp add: st_tcb_def2 split: if_split_asm)
  done

crunch etcb_at[wp]: update_sched_context "etcb_at P t"

lemma update_sched_context_valid_sched[wp]:
  "\<lbrace>valid_sched and K (\<forall>sc. 0 < sc_refill_max sc \<longrightarrow> 0 < sc_refill_max (f sc))\<rbrace>
    update_sched_context ptr f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def
          wp: update_sched_context_valid_etcbs update_sched_context_valid_queues)


context DetSchedSchedule_AI begin

lemma choose_thread_ct_not_queued:
  "\<lbrace> valid_queues and valid_idle and valid_etcbs \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_not_queued \<rbrace>"
  by (wpsimp simp: choose_thread_def wp: guarded_switch_to_lift)

lemma choose_thread_ct_activatable:
  "\<lbrace> valid_queues and valid_idle \<rbrace> choose_thread \<lbrace>\<lambda>_ s.  st_tcb_at activatable (cur_thread s) s \<rbrace>"
  apply (wpsimp simp: choose_thread_def
                wp: guarded_switch_to_lift stit_activatable'[simplified ct_in_state_def]
                    stt_activatable[simplified ct_in_state_def])
  apply (fastforce dest!: next_thread_queued
                   simp: next_thread_def valid_queues_def is_activatable_def in_cur_domain_def)
  done

lemma choose_thread_cur_dom_or_idle:
  "\<lbrace> valid_queues \<rbrace>
   choose_thread
   \<lbrace>\<lambda>_ s. (in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s) \<rbrace>"
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

crunch sched_act[wp]: choose_thread "\<lambda>s. P (scheduler_action s)"
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
  "wrap_is_highest_prio cur_dom target_prio \<equiv> NonDetMonad.gets (is_highest_prio cur_dom target_prio)"

lemma schedule_choose_new_thread_valid_sched:
  "\<lbrace> valid_idle and valid_etcbs and valid_idle_etcb and valid_queues and valid_blocked
     and (\<lambda>s. scheduler_action s = choose_new_thread)
     and ct_in_q \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. valid_sched \<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp_del: hoare_when_wp
                 wp: set_scheduler_action_rct_valid_sched choose_thread_ct_not_queued
                     choose_thread_ct_activatable choose_thread_cur_dom_or_idle
                     hoare_vcg_disj_lift)+
    apply (wpsimp wp: next_domain_valid_sched_action next_domain_valid_etcbs
                      next_domain_valid_queues next_domain_valid_blocked next_domain_ct_in_q)+
  done


crunch valid_sched[wp]: cap_swap_for_delete, empty_slot valid_sched
  (simp: unless_def wp: maybeM_inv ignore: set_object)
crunch valid_etcbs[wp]: cap_swap_for_delete, empty_slot valid_etcbs
  (simp: unless_def wp: maybeM_inv ignore: set_object)

crunch valid_sched[wp]: commit_time,rollback_time valid_sched
  (ignore: update_sched_context simp: Let_def wp: get_sched_context_wp hoare_drop_imp)

crunch valid_sched[wp]: refill_unblock_check valid_sched
  (wp: get_refills_wp hoare_drop_imps hoare_vcg_if_lift2)

lemma switch_sched_context_valid_sched:
  "\<lbrace>valid_sched\<rbrace> switch_sched_context \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: switch_sched_context_def)
  apply (wpsimp split_del: if_split wp: hoare_drop_imps)
  done

lemma set_next_timer_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_timer_interrupt thread_time \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: set_next_timer_interrupt_def)
  by wpsimp

lemma set_next_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_next_interrupt \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: set_next_interrupt_def)
  by (wpsimp wp: hoare_drop_imp)

lemma sc_and_timer_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sc_and_timer \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: sc_and_timer_def)
  by (wpsimp simp: wp: switch_sched_context_valid_sched)

crunch ct_not_in_q[wp]: finalise_cap ct_not_in_q
  (wp: crunch_wps hoare_drop_imps hoare_unless_wp select_inv mapM_wp maybeM_inv
       subset_refl if_fun_split simp: crunch_simps ignore: tcb_sched_action)

end

lemma set_scheduler_action_swt_weak_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable t and schedulable_tcb_at t and (\<lambda>s. t \<notin> set (release_queue s))
      and in_cur_domain t and simple_sched_action\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  by (wpsimp simp: valid_sched_def ct_not_in_q_def valid_sched_action_def valid_blocked_def
                   weak_valid_sched_action_def switch_in_cur_domain_def simple_sched_action_def
       split: scheduler_action.splits)

lemma possible_switch_to_valid_sched[wp]:
  "\<lbrace>valid_sched and st_tcb_at runnable target and schedulable_tcb_at target
    and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
     possible_switch_to target \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding possible_switch_to_def ethread_get_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp simp: pred_tcb_at_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac sc_opt; clarsimp)
   apply wpsimp
  apply (wpsimp wp: reschedule_required_valid_blocked set_scheduler_action_swt_weak_valid_sched
         | strengthen valid_blocked_valid_blocked_except)+
  apply (clarsimp simp: etcb_at'_def not_cur_thread_2_def valid_sched_def valid_sched_action_def
                      in_cur_domain_def ct_in_cur_domain_2_def valid_blocked_def in_release_queue_def
                      valid_blocked_except_def get_etcb_SomeD pred_tcb_at_def obj_at_def
                split: option.splits)
  done

crunch etcb_at[wp]: awaken "etcb_at P t"
  (wp: hoare_drop_imps mapM_x_wp')

crunches is_schedulable
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  and valid_blocked[wp]: valid_blocked
  and switch_thread[wp]: "\<lambda>s. scheduler_action s = switch_thread t"
  and resume_cur_thread[wp]: "\<lambda>s. scheduler_action s = resume_cur_thread"
  and choose_new_thread[wp]: "\<lambda>s. scheduler_action s = choose_new_thread"
  and ct_in_q[wp]: ct_in_q
  and valid_idle[wp]: valid_idle
  and valid_etcbs[wp]: valid_etcbs
  and valid_queues[wp]: valid_queues
  and ct_in_q[wp]: ct_in_q
  and is_activatable[wp]: "is_activatable t"
  and in_cur_domain[wp]: "in_cur_domain t"
  and valid_sched_action[wp]: valid_sched_action

crunches awaken
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  and valid_idle[wp]: valid_idle
  and valid_etcbs[wp]: valid_etcbs
  and in_cur_domain[wp]: "in_cur_domain t"
  (wp: hoare_drop_imps mapM_x_wp')

crunches possible_switch_to
  for valid_idle_etcb[wp]: "valid_idle_etcb"
  and valid_idle[wp]: valid_idle
  and valid_etcbs[wp]: valid_etcbs
  and in_cur_domain[wp]: "in_cur_domain t"

lemma possible_switch_to_valid_queues[wp]:
  "\<lbrace>valid_queues and st_tcb_at runnable target\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding possible_switch_to_def ethread_get_def gets_the_def
  apply (rule hoare_seq_ext[OF _ gsc_sp])
   by wpsimp

lemma set_nonmember_if_cong: "(a \<notin> set (if P then x else y)) = (if P then a \<notin> set x else a \<notin> set y)"
  by auto

lemma switch_thread_valid_sched_is_schedulable:
  "\<lbrakk>scheduler_action s = switch_thread t; valid_sched s; x = in_release_queue t s\<rbrakk>
      \<Longrightarrow> the (is_schedulable_opt t x s)"
   apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def get_tcb_rev
                split: option.splits)
  by (clarsimp simp: is_schedulable_opt_def schedulable_tcb_at_def pred_tcb_at_def
                        test_sc_refill_max_def in_release_queue_def obj_at_def get_tcb_rev)

lemma set_scheduler_action_cnt_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_scheduler_action choose_new_thread  \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def schedulable_tcb_at_def)

lemma tcb_sched_action_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> tcb_sched_action action thread  \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def schedulable_tcb_at_def)

lemma reschedule_required_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> reschedule_required \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  by (wpsimp simp: reschedule_required_def)

lemma reschedule_preserves_valid_shed[wp]: "\<lbrace> valid_sched \<rbrace> reschedule_required \<lbrace> \<lambda>rv. valid_sched \<rbrace>"
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
   apply wpsimp
   apply (clarsimp simp only: etcb_at_def)
   apply (case_tac "ekheap s thread"; simp)
   apply (clarsimp simp: valid_sched_2_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_queues_2_def valid_sched_action_2_def tcb_sched_enqueue_def
                          weak_valid_sched_action_2_def etcb_at_conj_is_etcb_at)
   apply (rule conjI)
    apply (clarsimp simp: ct_not_in_q_2_def)
   apply (clarsimp simp: not_queued_def valid_blocked_2_def)
   apply (erule_tac x=t in allE; simp)
   apply (clarsimp simp:  set_nonmember_if_cong tcb_sched_enqueue_def split: if_split_asm; blast)
  apply (clarsimp simp: switch_thread_valid_sched_is_schedulable)
  done

lemma set_simple_ko_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  by (wp hoare_drop_imps valid_queues_lift | simp add: set_simple_ko_def)+

lemma set_simple_ko_pred_tcb_at [wp]:
  "\<lbrace> schedulable_tcb_at t \<rbrace>
   set_simple_ko g ep v
   \<lbrace> \<lambda>rv. schedulable_tcb_at t \<rbrace>"
  apply (wpsimp simp: set_simple_ko_def a_type_def partial_inv_def set_object_def the_equality
              schedulable_tcb_at_def pred_tcb_at_def obj_at_def wp: get_object_wp
             split: kernel_object.splits if_splits)
  apply (intro conjI impI allI; clarsimp simp: the_equality)
  by (rule_tac x=scp in exI; clarsimp)+

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

crunch etcb_at[wp]: set_simple_ko "etcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_ipc_valid_sched:
  "\<lbrace>valid_sched\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (wp mapM_x_wp' set_thread_state_runnable_valid_queues sts_st_tcb_at' hoare_drop_imps
          set_thread_state_runnable_weak_valid_sched_action hoare_vcg_all_lift
          set_thread_state_valid_blocked_except
          tcb_sched_action_enqueue_valid_blocked
          reschedule_required_valid_sched possible_switch_to_valid_idle_etcb
     | wpc
     | rule subset_refl | simp)+
    apply (simp_all add: valid_sched_def valid_sched_action_def)
    sorry

crunch etcb_at[wp]: set_notification "etcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

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
  sorry

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
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   \<lbrace>weak_valid_sched_action\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: weak_valid_sched_action_lift thread_set_no_change_tcb_state
                 schedulable_tcb_at_thread_set_no_change hoare_drop_imps
             simp: thread_set_def)

lemma thread_set_not_state_valid_sched:
  "(\<And>x. tcb_state (f x) = tcb_state x) \<Longrightarrow>
   (\<And>x. tcb_sched_context (f x) = tcb_sched_context x) \<Longrightarrow>
   \<lbrace>valid_sched\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wp hoare_drop_imps valid_sched_lift schedulable_tcb_at_thread_set_no_change
         thread_set_no_change_tcb_state|
      simp add: thread_set_def)+

lemma unbind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_notification ntfnptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptra, simp add: maybeM_def, wp, simp)
  apply (wpsimp wp: maybeM_inv set_bound_notification_valid_sched simp: update_sk_obj_ref_def)
  done

crunches test_reschedule
for valid_etcbs[wp]: valid_etcbs
and ekheap[wp]: "\<lambda>s. P (ekheap s)"
and valid_sched[wp]: valid_sched
  (wp: hoare_drop_imps hoare_vcg_if_lift2)

crunches update_sk_obj_ref,reply_unlink_tcb,tcb_release_remove,store_word_offs
for valid_etcbs[wp]: valid_etcbs
and ekheap[wp]: "\<lambda>s. P (ekheap s)"
  (simp: a_type_def wp: get_object_wp hoare_drop_imps)

lemma sched_context_donate_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> sched_context_donate scptr tptr \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: sched_context_donate_def set_tcb_obj_ref_def set_sc_obj_ref_def update_sched_context_def)

lemma reply_unlink_sc_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> reply_unlink_sc sc_ptr reply_ptr \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (clarsimp simp: reply_unlink_sc_def)
  apply (wpsimp wp: hoare_drop_imps valid_etcbs_lift
           simp: set_sc_obj_ref_def update_sched_context_def)
  done

crunch valid_etcbs[wp]: reply_remove,reply_remove_tcb,test_reschedule valid_etcbs
  (wp: hoare_drop_imps)

crunches reply_unlink_sc,tcb_release_remove
  for etcb_at[wp]: "etcb_at P t"
  and ekheap[wp]: "\<lambda>s. P (ekheap s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches test_reschedule
  for etcb_at[wp]: "etcb_at P t"
  and ekheap[wp]: "\<lambda>s. P (ekheap s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

crunches reply_unlink_tcb
  for etcb_at[wp]: "etcb_at P t"
  and ekheap[wp]: "\<lambda>s. P (ekheap s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

lemma sched_context_donate_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (case_tac "sc_tcb sc"; clarsimp)
   apply (wpsimp simp: set_tcb_obj_ref_def set_object_def set_sc_obj_ref_def
update_sched_context_def wp: get_object_wp)
apply (clarsimp dest!: get_tcb_SomeD split: if_split_asm simp: valid_sched_def obj_at_def)
apply (intro conjI)
apply (frule (1) valid_etcbs_ko_etcb)
apply (clarsimp simp: obj_at_def valid_etcbs_def
  st_tcb_at_kh_def obj_at_kh_def)
apply (drule_tac x=tcb_ptr in spec, clarsimp simp: is_etcb_at_def)
apply (fastforce simp: valid_queues_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
apply (clarsimp simp: valid_sched_action_def)
apply (rule conjI)
apply (fastforce simp: is_activatable_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_def schedulable_tcb_at_kh_def
bound_sc_tcb_at_kh_def obj_at_kh_def obj_at_def)
apply (intro impI conjI; clarsimp)
(*apply (clarsimp simp: valid_blocked_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)

apply (clarsimp simp: assert_opt_def bind_assoc)
   apply (wpsimp simp: set_tcb_obj_ref_def set_object_def set_sc_obj_ref_def
update_sched_context_def
 wp: hoare_vcg_all_lift hoare_drop_imp get_object_wp tcb_sched_action_dequeue_valid_sched_except_blocked)
 *) sorry

lemma reply_unlink_tcb_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_unlink_tcb param_a \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (wpsimp simp: set_thread_state_def
wp: set_thread_state_runnable_valid_sched_except_blocked)
  sorry

lemma reply_unlink_sc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_unlink_sc scptr rptr \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: reply_unlink_sc_def)
  apply (wpsimp simp: set_sc_obj_ref_def
wp: update_sched_context_valid_sched)
  apply (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sched_context_def set_object_def
               update_sk_obj_ref_def set_simple_ko_def
        wp: hoare_drop_imp get_object_wp get_simple_ko_wp get_sched_context_wp)
  sorry

lemma reply_remove_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> reply_remove param_a \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: reply_remove_def set_sc_obj_ref_def wp: hoare_drop_imp)

crunch valid_sched[wp]: reply_remove_tcb valid_sched

lemma unbind_maybe_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> unbind_maybe_notification param_a \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: unbind_maybe_notification_def)
  apply (wpsimp simp: unbind_maybe_notification_def set_tcb_obj_ref_def
             wp: set_simple_ko_valid_sched hoare_drop_imp)
sorry

crunch valid_sched[wp]: unbind_maybe_notification valid_sched
  (wp: maybeM_inv)

lemma sched_context_unbind_tcb_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> sched_context_unbind_tcb param_a \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: sched_context_unbind_tcb_def set_tcb_obj_ref_def set_sc_obj_ref_def update_sched_context_def)

lemma set_mrs_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift mapM_wp'
      simp: set_mrs_def zipWithM_x_mapM split_del: if_split)

lemma unbind_maybe_notification_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> unbind_maybe_notification ntfnptr \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: unbind_maybe_notification_def set_tcb_obj_ref_def get_sk_obj_ref_def)

lemma unbind_notification_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> unbind_notification ntfnptr \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: unbind_notification_def set_tcb_obj_ref_def get_sk_obj_ref_def)

lemma set_sched_context_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_sched_context scp new \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: set_sched_context_def set_tcb_obj_ref_def get_sk_obj_ref_def)

crunch valid_sched[wp]: reply_unlink_tcb valid_sched
  (simp: wp: maybeM_inv get_simple_ko_wp ignore: set_object)

crunches set_mrs,set_message_info,set_consumed,reply_unlink_sc
  for etcb_at[wp]: "etcb_at P t"
  and ekheap[wp]: "\<lambda>s. P (ekheap s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (simp: zipWithM_x_mapM wp: mapM_wp' hoare_drop_imp)

lemma as_user_schedulable_tcb_at [wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> as_user t' m \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  by (wp as_user_wp_thread_set_helper schedulable_tcb_at_thread_set_no_change
      | simp add: thread_set_def)+

lemma set_message_info_pred_tcb_at[wp]:
  "\<lbrace>(\<lambda>s. schedulable_tcb_at t s)\<rbrace>
    set_message_info tptr f \<lbrace>\<lambda>_ s. schedulable_tcb_at t s\<rbrace>"
  by (wpsimp split_del: if_split simp: set_message_info_def split_def set_object_def)

crunches set_mrs,set_message_info
  for schedulable_tcb_at[wp]: "schedulable_tcb_at t"
  (wp: crunch_wps simp: crunch_simps)

crunches do_machine_op
for ready_queue[wp]: "\<lambda>s. P (ready_queues s)"
  (ignore: set_object do_machine_op simp: zipWithM_x_mapM wp: mapM_wp')

lemma set_mrs_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp:  wp: valid_sched_lift)

lemma set_message_info_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_message_info thread info \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp:  wp: valid_sched_lift)

lemma complete_yield_to_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> complete_yield_to tp \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: hoare_drop_imps valid_etcbs_lift
      simp: complete_yield_to_def set_tcb_obj_ref_def set_sc_obj_ref_def
            get_sk_obj_ref_def update_sched_context_def)

(* FIXME: Move to SchedContext_AI *)
lemma ssc_sc_yf_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

(* FIXME: Move to SchedContext_AI *)
lemma set_tcb_yt_update_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_yield_to_update scp tcb \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def pred_tcb_at_def obj_at_def get_tcb_rev)

(* FIXME: Move to SchedContext_AI *)
lemma ssc_sc_yf_update_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_sc_obj_ref sc_yield_from_update scp tcb \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def wp: schedulable_tcb_at_update_sched_context_no_change)

(* FIXME: Move to SchedContext_AI *)
lemma set_tcb_yt_update_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_tcb_obj_ref tcb_yield_to_update scp tcb \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  by (auto intro: schedulable_tcb_at_set_object_no_change_tcb)


crunches store_word_offs,set_mrs
  for schedulable_tcb_at[wp]: "schedulable_tcb_at t"
  (simp: zipWithM_x_mapM wp: dmo_schedulable_tcb_at mapM_wp' schedulable_tcb_at_set_object_no_change_sc ignore: set_sched_context)

lemma sched_context_update_consumed_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>y. schedulable_tcb_at t\<rbrace>"
  apply (clarsimp simp: sched_context_update_consumed_def set_sched_context_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: schedulable_tcb_at_def pred_tcb_at_def obj_at_def)
  apply (rule conjI; clarsimp)
  apply (rule_tac x=scpa in exI, clarsimp)
  done

lemma set_consumed_schedulable_tcb_at[wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> set_consumed scp buf \<lbrace>\<lambda>_. schedulable_tcb_at t\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_consumed_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_consumed scp buf \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp wp: valid_sched_lift split_del: if_split)

lemma complete_yield_to_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> complete_yield_to tp \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def
      get_sk_obj_ref_def)
              apply (wpsimp simp: set_tcb_obj_ref_def wp: hoare_drop_imp)+
  by (wpsimp wp: hoare_drop_imps valid_sched_lift
      simp: complete_yield_to_def update_sched_context_def set_tcb_obj_ref_def
      get_sk_obj_ref_def)+

(*
crunch valid_sched[wp]: sched_context_unbind_all_tcbs,sched_context_clear_replies,suspend valid_sched
  (wp: valid_sched_lift ignore: tcb_release_remove set_tcb_queue)
*)
crunch valid_etcbs[wp]: reply_unlink_sc valid_etcbs
  (wp: valid_etcbs_lift mapM_x_wp')
(*
crunch valid_etcbs[wp]: sched_context_unbind_tcb,sched_context_unbind_all_tcbs,sched_context_clear_replies,suspend valid_etcbs
  (wp: valid_etcbs_lift mapM_x_wp' get_sched_context_wp hoare_vcg_if_lift2 hoare_drop_imps)
*)

lemma set_tcb_yt_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_tcb_obj_ref tcb_yield_to_update tp new \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_def obj_at_kh_def obj_at_def is_etcb_at_def
           dest!: get_tcb_SomeD)
  done

lemma set_tcb_sc_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> set_tcb_obj_ref tcb_sched_context_update tp new \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (wpsimp simp: set_object_def)
  apply (fastforce simp: valid_etcbs_def st_tcb_at_kh_def obj_at_kh_def obj_at_def is_etcb_at_def
           dest!: get_tcb_SomeD)
  done

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
  apply (simp add:  set_object_def | wp)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split ct_not_in_q_def
                         st_tcb_at_not)
  done

lemma set_thread_state_not_runnable_valid_blocked:
  "\<lbrace>valid_blocked and K (\<not> runnable ts)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def set_object_def | wp)+
       apply (rule hoare_strengthen_post)
       apply (rule set_scheduler_action_cnt_valid_blocked_weak)
      apply simp
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp gts_wp)+
apply (clarsimp simp: cong: conj_cong)
  apply (clarsimp simp: valid_blocked_def dest!: get_tcb_SomeD)
  apply (case_tac ts, simp_all)
  (*done*) sorry

lemma set_thread_state_not_runnable_weak_valid_sched_action:
  "\<lbrace>weak_valid_sched_action and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
      set_thread_state ref ts \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def set_object_def
           wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp)
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                        bound_sc_tcb_at_kh_if_split st_tcb_at_not schedulable_tcb_at_kh_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb dest!: get_tcb_SomeD)
  apply (intro conjI impI)
  sorry

lemma set_thread_state_not_runnable_valid_sched_action:
  "\<lbrace>valid_sched_action and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) ref s)\<rbrace>
      set_thread_state ref ts
   \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: valid_sched_action_def |
         wp set_thread_state_not_runnable_weak_valid_sched_action)+
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


lemma cancel_signal_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     cancel_signal tptr ntfnptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wp set_thread_state_not_runnable_valid_sched hoare_drop_imps | wpc | simp)+
  done

lemma blocked_cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s)\<rbrace>
     blocked_cancel_ipc ts tptr reply_opt
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp set_thread_state_not_runnable_valid_sched)
  apply simp
  sorry

lemma tcb_release_remove_valid_sched_def[wp]:
  "\<lbrace>valid_sched\<rbrace> tcb_release_remove tp \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: tcb_release_remove_def)
  by (clarsimp simp: valid_sched_def valid_sched_action_def
                weak_valid_sched_action_def tcb_sched_dequeue_def)

context DetSchedSchedule_AI begin

crunch valid_etcbs[wp]: cap_delete_one valid_etcbs
  (wp: maybeM_inv mapM_x_wp' simp: unless_def)

lemma suspend_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> suspend tp \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  by (wpsimp wp: maybeM_inv simp: suspend_def)

crunch valid_etcbs[wp]: finalise_cap,fast_finalise valid_etcbs
  (wp: hoare_drop_imps hoare_unless_wp select_inv mapM_x_wp mapM_wp subset_refl maybeM_inv
       if_fun_split hoare_vcg_if_lift2 simp: crunch_simps set_tcb_obj_ref_def
   ignore: set_object sched_context_unbind_all_tcbs sched_context_clear_replies suspend
           reply_cancel_ipc)

crunch valid_sched[wp]: sched_context_unbind_yield_from,sched_context_clear_replies "valid_sched"
  (wp: maybeM_inv mapM_x_wp')

lemma sched_context_unbind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_unbind_ntfn scptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: sched_context_unbind_ntfn_def set_sc_obj_ref_def get_sc_obj_ref_def update_sk_obj_ref_def)

lemma sched_context_maybe_unbind_ntfn_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> sched_context_maybe_unbind_ntfn scptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: sched_context_maybe_unbind_ntfn_def get_sk_obj_ref_def)

lemma cancel_ipc_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)
  apply (fastforce elim!: st_tcb_weakenE)
  done
(*
lemma fast_finalise_valid_sched[wp]:
  "\<lbrace>valid_sched \<rbrace> fast_finalise cap b \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (cases cap; wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp get_simple_ko_inv)

crunch valid_sched[wp]: fast_finalise valid_sched

lemma cap_delete_one_valid_sched[wp]:
  "\<lbrace>valid_sched \<rbrace> cap_delete_one slot \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: cap_delete_one_def)
  apply (wpsimp simp: unless_def hoare_vcg_if_lift2 wp: get_cap_wp)
  done

crunch valid_sched[wp]: cap_delete_one valid_sched
  (simp: unless_def wp: maybeM_inv hoare_vcg_if_lift2 hoare_drop_imp
   ignore: fast_finalise)
*)
end

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
crunch simple_sched_action[wp]: set_thread_state_ext simple_sched_action
  (wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma set_thread_state_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_thread_state param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: set_thread_state_def)

lemma possible_switch_to_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  apply (clarsimp simp: possible_switch_to_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp simp: possible_switch_to_def get_tcb_obj_ref_def
     wp: thread_get_wp hoare_drop_imp)
  apply (clarsimp simp: pred_tcb_at_def etcb_at'_def obj_at_def simple_sched_action_2_def
     split: option.splits scheduler_action.splits)
  sorry

crunch simple[wp]: set_sc_obj_ref,tcb_sched_action,update_sched_context,
set_tcb_obj_ref,tcb_release_remove,sched_context_donate simple_sched_action

crunch simple[wp]: update_sk_obj_ref,reply_unlink_sc,reply_unlink_tcb,reply_remove simple_sched_action
  (simp: a_type_def wp: hoare_drop_imps)

lemma sched_context_unbind_tcb_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)

crunch simple[wp]: store_word_offs simple_sched_action

lemma set_mrs_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: set_mrs_def zipWithM_x_mapM wp: mapM_wp' split_del: if_split)

context DetSchedSchedule_AI begin

crunch simple_sched_action[wp]: finalise_cap simple_sched_action
  (wp: hoare_drop_imps mapM_x_wp mapM_wp select_wp subset_refl maybeM_inv
   simp: unless_def if_fun_split)

lemma suspend_valid_sched[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> suspend t \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
apply (simp add: suspend_def)
apply (rule seq_ext)
 apply (rule_tac R="K $ valid_sched and simple_sched_action" in hoare_strengthen_post[rotated])
  apply (wp tcb_sched_action_dequeue_strong_valid_sched
       | simp)+
    apply (simp add: set_thread_state_def)
    apply (wpsimp wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imp split_del: if_split
           simp: set_thread_state_ext_def
                     reschedule_required_def set_scheduler_action_def
                     tcb_sched_action_def set_object_def simp_del: fun_upd_apply)+
    apply (simp only: st_tcb_at_kh_simp[symmetric])
    apply (clarsimp simp: valid_sched_def valid_queues_def st_tcb_at_kh_if_split
                          valid_sched_action_def simple_sched_action_def
                          is_activatable_def valid_blocked_def
                    split: scheduler_action.splits)+
    sorry

lemma finalise_cap_valid_sched[wp]:
  "\<lbrace>valid_sched and (valid_etcbs and valid_queues and weak_valid_sched_action and
    valid_blocked and valid_idle_etcb and simple_sched_action)\<rbrace>
      finalise_cap cap param_b \<lbrace>\<lambda>_. valid_sched\<rbrace>"  (* check the preconditions *)
  apply (case_tac cap; wpsimp)

  sorry
(*
crunch valid_sched[wp]: finalise_cap valid_sched
  (wp: crunch_wps maybeM_inv simp: crunch_simps)
*)
end

crunch simple_sched_action[wp]: cap_swap_for_delete, cap_insert simple_sched_action
  (wp: mapM_wp subset_refl hoare_drop_imps)

context DetSchedSchedule_AI begin

lemma rec_del_valid_sched'[wp]:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace>
    rec_del call
   \<lbrace>\<lambda>rv. valid_sched and simple_sched_action\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wpsimp wp: preemption_point_inv' | simp)+
  sorry

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

lemma tcb_dequeue_not_queued_gen:
  "\<lbrace>not_queued tptr\<rbrace> tcb_sched_action tcb_sched_dequeue tptr' \<lbrace>\<lambda>_. not_queued tptr\<rbrace>"
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

crunches reorder_ntfn,reorder_ep
  for valid_sched[wp]: valid_sched
  and simple_sched_action[wp]: simple_sched_action
  (wp: mapM_wp' get_simple_ko_wp)

lemma set_priority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_priority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: set_priority_def thread_set_priority_def)
   apply (wpsimp wp: gts_wp hoare_vcg_if_lift ethread_set_not_queued_valid_queues
              hoare_vcg_all_lift
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
           simp: ct_in_state_def2[symmetric])+
  apply (force simp: valid_sched_def valid_sched_action_def
                not_cur_thread_def ct_in_state_def not_pred_tcb st_tcb_at_def obj_at_def)
  done

lemma set_mcpriority_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> set_mcpriority tptr prio \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (simp add: set_mcpriority_def thread_set_not_state_valid_sched)

crunch simple_sched_action[wp]: set_mcpriority,thread_set_priority simple_sched_action
  (wp: maybeM_inv)
crunch simple_sched_action[wp]: sort_queue simple_sched_action
  (wp: maybeM_inv mapM_wp)

lemma set_priority_simple_sched_action[wp]:
  "\<lbrace>simple_sched_action\<rbrace> set_priority param_a param_b \<lbrace>\<lambda>_. simple_sched_action\<rbrace>"
  by (wpsimp simp: set_priority_def)

context DetSchedSchedule_AI begin

crunch valid_sched[wp]: arch_tcb_set_ipc_buffer valid_sched

lemma tc_valid_sched[wp]:
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
(*   by (wp check_cap_inv thread_set_not_state_valid_sched hoare_vcg_all_lift gts_wp static_imp_wp
         | wpc | simp add: option_update_thread_def | rule reschedule_preserves_valid_shed
         | wp_once hoare_drop_imps )+*)
  sorry


end

crunch not_cur_thread[wp]: schedule_tcb "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma set_thread_state_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread thread\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv. not_cur_thread thread\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_thread_state_ext_def  set_object_def
         wp: hoare_vcg_if_lift2 hoare_drop_imp gts_wp)+
  done

crunch not_cur_thread[wp]: reply_remove "not_cur_thread thread"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma set_scheduler_action_cnt_valid_blocked_except:
  "\<lbrace>\<lambda>s. valid_blocked_except target s
        \<and> (\<forall>t. scheduler_action s = switch_thread t \<longrightarrow> \<not> not_queued t s) \<rbrace>
   set_scheduler_action choose_new_thread
   \<lbrace>\<lambda>rv. valid_blocked_except target\<rbrace>"
  apply (wpsimp wp: set_scheduler_action_wp)
  apply (fastforce simp: valid_blocked_except_def simple_sched_action_def
                   split: scheduler_action.splits)
  done

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

crunch valid_sched[wp]: test_possible_switch_to valid_sched
  (wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma awaken_valid_queues:
  "\<lbrace>valid_queues\<rbrace> awaken \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  unfolding awaken_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: mapM_x_wp)
apply (clarsimp simp: valid_queues_def)
sorry


lemma awaken_valid_sched_helper:
  "\<lbrace>valid_sched and (\<lambda>s. \<forall>t. t \<in> set queue \<longrightarrow> (t \<noteq> idle_thread s \<and> not_cur_thread t s))\<rbrace>
         mapM_x (\<lambda>t. do possible_switch_to t;
                        modify (reprogram_timer_update (\<lambda>_. True))
                     od) queue \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  sorry

lemma awaken_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. \<forall>t. in_release_queue t s \<longrightarrow> (t \<noteq> idle_thread s \<and> not_cur_thread t s))\<rbrace>
   awaken \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding awaken_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp wp: awaken_valid_sched_helper)
  by (auto simp: in_release_queue_def dest!: set_takeWhileD)

crunches sc_and_timer
for valid_idle[wp]: "valid_idle::det_ext state \<Rightarrow> bool"
  (wp: hoare_drop_imps)

crunches awaken
for cur_tcb[wp]: cur_tcb
  (wp: hoare_drop_imps mapM_x_wp')


context DetSchedSchedule_AI begin



lemma schedule_valid_sched:
  "\<lbrace>valid_sched and valid_idle (*and cur_tcb and (\<lambda>s. \<not>in_release_queue (cur_thread s) s)*)\<rbrace>
     schedule \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding schedule_def
  supply ethread_get_wp[wp del]
apply (rule hoare_pre)
apply (rule hoare_seq_ext[OF _ hoare_vcg_conj_lift[OF awaken_valid_sched awaken_valid_idle
                                  (*hoare_vcg_conj_lift[OF awaken_valid_idle awaken_cur_tcb]*)]])
apply clarsimp
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (case_tac action; clarsimp simp: bind_assoc)
         (* resume_cur_thread *)
         apply wpsimp
        prefer 2
        (* choose new thread *)
        apply (case_tac ct_schedulable; clarsimp)
        apply (wpsimp wp: schedule_choose_new_thread_valid_sched tcb_sched_action_enqueue_valid_blocked
                   tcb_sched_enqueue_cur_ct_in_q split_del: if_split)
 apply (clarsimp simp: valid_sched_def)

subgoal for ct_schedulable s
apply (insert ct_assumptions, drule_tac x=s in meta_spec)
apply (clarsimp simp: valid_blocked_def valid_blocked_except_def is_schedulable_opt_def)
apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev)
done

apply (wpsimp wp: schedule_choose_new_thread_valid_sched)

subgoal for cts s
apply (insert ct_assumptions, drule_tac x=s in meta_spec)
apply (clarsimp simp: is_schedulable_opt_def)
apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev valid_sched_def)
sorry
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
  sorry


crunch not_cur_thread[wp]: cancel_ipc "not_cur_thread thread"
  (wp: hoare_drop_imps select_wp mapM_x_wp simp: unless_def if_fun_split)


lemma restart_valid_sched[wp]:
  "\<lbrace>valid_sched and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace> restart thread \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: restart_def | wp set_thread_state_runnable_valid_queues
                                    set_thread_state_runnable_valid_sched_action
                                    set_thread_state_valid_blocked_except
                                    sts_st_tcb_at' cancel_ipc_simple2
                                    possible_switch_to_valid_sched)+
    apply (rule_tac Q="\<lambda>_. valid_sched and not_cur_thread thread and (\<lambda>s. thread \<noteq> idle_thread s)" in hoare_strengthen_post)
     apply wp
    apply (simp add: valid_sched_def)
   apply (simp add: if_fun_split)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: get_thread_state_def thread_get_def)
    apply wp
(*
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
(*
  apply (simp only: st_tcb_at_not)
  apply simp
  done
*)
  apply (simp add: get_thread_state_def | wp hoare_drop_imps)+
  done*) sorry


end

lemma bind_notification_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> bind_notification param_a param_b \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: bind_notification_def update_sk_obj_ref_def)
  apply (wpsimp simp: set_object_def set_simple_ko_def
          wp: get_simple_ko_wp hoare_drop_imp set_bound_notification_valid_sched)
  done

lemma suspend_it_det_ext[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> suspend param_a \<lbrace>\<lambda>_ s::det_ext state. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: suspend_def)

context DetSchedSchedule_AI begin
lemma invoke_tcb_valid_sched[wp]:
  "\<lbrace>invs and valid_sched and simple_sched_action and tcb_inv_wf ti\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases ti, simp_all only:)
(*
        apply (wp mapM_x_wp | simp | rule subset_refl | rule reschedule_preserves_valid_sched |
               clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap |
               intro impI conjI)+
    apply (rename_tac option)
    apply (case_tac option)
     apply (wp mapM_x_wp | simp | rule subset_refl |
            clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap |
            rule reschedule_preserves_valid_sched | intro impI conjI)+
  done
*)
        apply (wp mapM_x_wp | simp | rule subset_refl | rule reschedule_preserves_valid_shed | clarsimp simp:invs_valid_objs invs_valid_global_refs idle_no_ex_cap | intro impI conjI)+
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
  sorry

crunch valid_sched[wp]: store_word_offs valid_sched

crunch exst[wp]: set_mrs, as_user "\<lambda>s. P (exst s)"
  (simp: crunch_simps wp: crunch_wps)

crunch ct_not_in_q[wp]: as_user ct_not_in_q
  (wp: ct_not_in_q_lift)

crunch valid_sched_action[wp]: as_user valid_sched_action
  (wp: valid_sched_action_lift)

crunch ct_in_cur_domain[wp]: as_user ct_in_cur_domain
  (wp: ct_in_cur_domain_lift)

lemmas gts_drop_imp = hoare_drop_imp[where f="get_thread_state p" for p]

lemma set_scheduler_action_swt_weak_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except t and st_tcb_at runnable t
     and schedulable_tcb_at t and in_cur_domain t and simple_sched_action and (\<lambda>s. \<not> in_release_queue t s)\<rbrace>
     set_scheduler_action (switch_thread t)
   \<lbrace>\<lambda>_.valid_sched\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  by (force simp: valid_sched_def ct_not_in_q_def valid_sched_action_def
     weak_valid_sched_action_def in_cur_domain_def ct_in_cur_domain_def in_release_queue_def
     switch_in_cur_domain_def valid_blocked_def valid_blocked_except_def simple_sched_action_def
      split: scheduler_action.splits)

lemma enqueue_thread_not_not_queued:
  "\<lbrace>\<lambda>s. t = thread \<rbrace>
     tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_ s. \<not> not_queued t s \<rbrace>"
  apply (simp add: tcb_sched_action_def not_queued_def)
  apply wp
  apply (fastforce simp: etcb_at_def tcb_sched_enqueue_def
                  split: option.splits)
  done

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

crunch scheduler_action[wp]: tcb_sched_action "\<lambda>s. P (scheduler_action s)"

crunch valid_etcbs[wp]: possible_switch_to "valid_etcbs"

lemma possible_switch_to_valid_sched':
  "\<lbrace>valid_sched_except_blocked and valid_blocked_except target and st_tcb_at runnable target
      and not_cur_thread target and (\<lambda>s. target \<noteq> idle_thread s)\<rbrace>
    possible_switch_to target
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding possible_switch_to_def reschedule_required_def
  apply (wpsimp simp: reschedule_required_def bind_assoc
                wp: set_scheduler_action_cnt_valid_blocked_except
                    tcb_sched_action_enqueue_valid_blocked_except
                    hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (wp enqueue_thread_not_not_queued)
  apply (wpsimp wp: set_scheduler_action_swt_weak_valid_sched')+
(*  apply (fastforce simp: in_cur_domain_def valid_sched_action_def
                          weak_valid_sched_action_def etcb_at_def
                   split: option.splits)
  done*) sorry

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
   apply (wp static_imp_wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a)
   apply (rule hoare_convert_imp)
    apply (rule typ_at_st_tcb_at_lift)
     apply (wp a t)+
  apply (simp add: valid_blocked_except_def)
  done

lemma as_user_valid_blocked_except[wp]:
 "\<lbrace>valid_blocked_except thread\<rbrace> as_user param_a param_b \<lbrace>\<lambda>_. valid_blocked_except thread\<rbrace>"
  by (wpsimp wp: valid_blocked_except_lift)

(* FIXME: Move *)
lemma set_simple_ko_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_simple_ko f ptr ntfn \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  by (wp hoare_drop_imps valid_sched_action_lift | simp add: set_simple_ko_def)+

crunch not_cur_thread[wp]: cap_insert_ext "not_cur_thread t"

crunch not_cur_thread[wp]: cap_insert, set_extra_badge "not_cur_thread t"
  (wp: hoare_drop_imps)

lemma transfer_caps_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread t\<rbrace> transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+


crunch not_cur_thread[wp]: as_user "not_cur_thread t"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

crunch (in DetSchedSchedule_AI) not_cur_thread[wp] : do_ipc_transfer "not_cur_thread t"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure)

lemmas set_thread_state_active_valid_sched_except_blocked =
  set_thread_state_runnable_valid_sched_except_blocked[simplified runnable_eq_active]

lemma set_thread_state_runnable_valid_blocked:
  "\<lbrace>valid_blocked and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_object_def | wp)+
     apply (clarsimp simp: set_thread_state_ext_def)
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ gets_sp])
     apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
     apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp set_scheduler_action_cnt_valid_blocked_weak
                   split_del: if_split)
     apply simp
    apply (wpsimp wp: hoare_vcg_if_lift2 gts_wp split_del: if_split)+
  apply (clarsimp simp: valid_blocked_def st_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def get_tcb_rev)
  apply (case_tac "tcb_state y"; clarsimp)
  done

lemma set_thread_state_runnable_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at runnable ref and (\<lambda>s. runnable ts)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def | wp set_thread_state_runnable_valid_queues
                                        set_thread_state_runnable_valid_sched_action
                                        set_thread_state_runnable_valid_blocked)+
  done

crunches test_reschedule
for valid_sched[wp]: valid_sched
and valid_etcbs[wp]: valid_etcbs
and valid_queues[wp]: valid_queues
and ct_not_in_q[wp]: ct_not_in_q
  (wp: maybeM_inv hoare_vcg_if_lift2)

crunches sched_context_donate,maybe_donate_sc
for valid_sched[wp]: valid_sched
and valid_etcbs[wp]: valid_etcbs
  (wp: maybeM_inv)

context DetSchedSchedule_AI begin
lemma update_waiting_ntfn_valid_sched[wp]:
  "\<lbrace> \<lambda>s. valid_sched s \<and> 
     hd queue \<noteq> idle_thread s \<and> (scheduler_action s = resume_cur_thread \<longrightarrow> hd queue \<noteq> cur_thread s)\<rbrace>
       update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (wp sts_st_tcb_at' possible_switch_to_valid_sched'
            set_thread_state_runnable_valid_sched
            set_thread_state_runnable_valid_queues
            set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except
            | clarsimp)+
  apply (clarsimp simp add: valid_sched_def not_cur_thread_def ct_not_in_q_def)
  sorry

end

crunch valid_sched[wp]: dec_domain_time valid_sched

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
  sorry

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

lemma thread_set_state_eq_valid_queues:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_queues and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_valid_sched_action:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow> (\<And>x. bound (tcb_sched_context (f x))) \<Longrightarrow>
   \<lbrace>valid_sched_action and st_tcb_at ((=) ts) tptr and schedulable_tcb_at tptr\<rbrace>
      thread_set f tptr \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply clarsimp
(*  apply (fast force simp: valid_sched_action_def weak_valid_sched_action_def bound_sc_tcb_at_kh_if_split
                         is_activatable_def st_tcb_at_kh_if_split st_tcb_def2
                   dest!: get_tcb_SomeD)*)
  sorry

lemma thread_set_state_eq_ct_in_cur_domain:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>ct_in_cur_domain and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: ct_in_cur_domain_def st_tcb_at_kh_if_split st_tcb_def2)
  done

lemma thread_set_state_eq_valid_blocked:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow>
   \<lbrace>valid_blocked and st_tcb_at ((=) ts) tptr\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (fastforce simp: valid_blocked_def st_tcb_at_kh_if_split st_tcb_def2)
  done

crunch etcb_at[wp]: thread_set "etcb_at P t"

context DetSchedSchedule_AI begin
lemma thread_set_state_eq_valid_sched:
  "(\<And>x. tcb_state (f x) = ts) \<Longrightarrow> (\<And>x. bound (tcb_sched_context (f x))) \<Longrightarrow>
   \<lbrace>valid_sched and st_tcb_at ((=) ts) tptr and schedulable_tcb_at tptr\<rbrace>
      thread_set f tptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
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

lemma do_ipc_transfer_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace>
    do_ipc_transfer param_a param_b param_c param_d param_e \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  sorry

crunch valid_sched[wp]: handle_fault_reply valid_sched
  (wp: crunch_wps)

lemma thread_set_ct_active_wp:
  "\<lbrace> ct_active \<rbrace> thread_set (tcb_fault_update u) t \<lbrace>\<lambda>rv. ct_active \<rbrace>"
  by (wpsimp wp: ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            simp: thread_set_def)

lemma do_reply_transfer_valid_sched[wp]:
  "\<lbrace>valid_sched and valid_objs and ct_active and cte_wp_at ((=) (ReplyCap t')) slot
       and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp set_thread_state_not_runnable_valid_sched sts_st_tcb_at'
            do_ipc_transfer_non_null_cte_wp_at2
            thread_set_not_state_valid_sched thread_set_no_change_tcb_state
            possible_switch_to_valid_sched'
         | wpc | clarsimp split del: if_split)+
(*        apply (wp set_thread_state_runnable_valid_queues
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
  done*) sorry

end

lemma set_thread_state_not_queued_valid_queues:
  "\<lbrace>valid_queues and not_queued thread\<rbrace>
      set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add:  set_object_def)+
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
   apply (wpsimp wp: gts_wp hoare_vcg_if_lift2 get_object_wp hoare_drop_imp split_del: if_splits
            simp: set_thread_state_ext_def set_object_def)
   apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                         scheduler_act_not_def is_activatable_def pred_tcb_at_def
                         obj_at_def dest!: get_tcb_SomeD)
(*  apply (wp gts_wp | simp add:  set_object_def)+
  apply (clarsimp simp: weak_valid_sched_action_def st_tcb_at_kh_if_split
                        scheduler_act_not_def is_activatable_def)
  done*) sorry

lemma set_thread_state_sched_act_not_valid_sched:
  "\<lbrace>valid_sched and scheduler_act_not thread
      and not_queued thread and K (\<not> runnable ts)\<rbrace>
     set_thread_state thread ts
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (simp add: valid_sched_def |
      wp set_thread_state_not_queued_valid_queues
                                    set_thread_state_not_runnable_valid_blocked
         set_thread_state_sched_act_not_valid_sched_action)+

(* strong in case of tcb_domain t = tcb_domain target *)
lemma possible_switch_to_sched_act_not[wp]:
  "\<lbrace>K(t \<noteq> target) and scheduler_act_not t\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def get_tcb_obj_ref_def
              split del: if_split
        | wp | wpc)+
  apply (clarsimp simp: etcb_at_def scheduler_act_not_def split: option.splits)
  sorry


lemma possible_switch_to_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t and K(target \<noteq> t)\<rbrace>
     possible_switch_to target
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: possible_switch_to_def reschedule_required_def
                   set_scheduler_action_def tcb_sched_action_def split del: if_split | wp | wpc)+
(*  by (fastforce simp: etcb_at_def tcb_sched_enqueue_def simple_sched_action_def
                         not_queued_def scheduler_act_not_def
                   split: option.splits)*) sorry

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
  (wp: crunch_wps ignore: const_on_failure rule: transfer_caps_loop_pres)

crunch ready_queues[wp]: cap_insert_ext "\<lambda>s :: det_ext state. P (ready_queues s)"

crunch ready_queues[wp]: cap_insert,set_extra_badge,do_ipc_transfer, set_simple_ko, thread_set "\<lambda>s :: det_state. P (ready_queues s)"
  (wp: crunch_wps transfer_caps_loop_pres ignore: const_on_failure)

end

crunch sched_act_not[wp]: set_simple_ko "scheduler_act_not t"
  (wp: hoare_drop_imps crunch_wps)

lemma set_thread_state_ext_sched_act_not[wp]:
  "\<lbrace>scheduler_act_not t\<rbrace> set_thread_state_ext tp  \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (clarsimp simp: set_thread_state_ext_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_inv])
  apply (wpsimp simp: set_scheduler_action_def)
  done

crunch sched_act_not[wp]: set_thread_state "scheduler_act_not t"

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

lemma reply_push_valid_sched:
  "\<lbrace>valid_sched\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  sorry

lemma reply_push_valid_etcbs:
  "\<lbrace>valid_etcbs\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  sorry

lemma reply_push_valid_queues:
  "\<lbrace>valid_queues\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (clarsimp simp: reply_push_def)
  sorry

crunches set_thread_state_ext
for ct_not_in_q[wp]: ct_not_in_q
and ct_active[wp]: ct_active
  (wp: crunch_wps ignore: set_object )

crunches reply_push
for ct_not_in_q[wp]: ct_not_in_q
(*and ct_active[wp]: ct_active*)
  (wp: crunch_wps ignore: set_thread_state)

context DetSchedSchedule_AI begin
lemma send_ipc_valid_sched:
  "\<lbrace>valid_sched  and scheduler_act_not thread and not_queued thread (*and st_tcb_at active thread
      and (ct_active or ct_idle) and invs*)\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep; clarsimp)
    apply (case_tac block; clarsimp)
     apply (wpsimp wp: set_thread_state_sched_act_not_valid_sched)
    apply wpsimp
   apply (case_tac block; clarsimp)
    apply (wpsimp wp: set_thread_state_sched_act_not_valid_sched)
   apply wpsimp
  apply (rename_tac ep_queue)
  apply (case_tac ep_queue; clarsimp)
  apply (rule hoare_seq_ext)
  apply (rule hoare_seq_ext[OF _ gts_sp])
apply (case_tac recv_state; clarsimp simp: bind_assoc maybeM_def)
apply (wpsimp)
       apply (wp set_thread_state_runnable_valid_sched
                 set_thread_state_runnable_valid_queues
                 set_thread_state_runnable_valid_sched_action
                 set_thread_state_valid_blocked_except sts_st_tcb_at')

apply (case_tac list; clarsimp simp: set_simple_ko_def bind_assoc)
(*  apply (rule hoare_seq_ext[OF _ get_object_sp])
apply_trace (wpsimp simp: partial_inv_def set_object_def bind_assoc)


  apply (rule hoare_seq_ext[OF _ get_sp])
  apply (rule hoare_seq_ext[])

apply (wpsimp wp: set_thread_state_Running_valid_sched set_thread_state_runnable_valid_queues
                  set_thread_state_runnable_weak_valid_sched_action set_thread_state_runnable_valid_blocked)
apply (wpsimp wp: reply_push_valid_sched reply_push_valid_etcbs reply_push_valid_queues)

            apply ((wp set_thread_state_sched_act_not_valid_sched
                       possible_switch_to_valid_sched'
                       hoare_vcg_if_lift2 hoare_drop_imps | simp)+)[5]
       apply (wp set_thread_state_runnable_valid_queues
                 set_thread_state_runnable_valid_sched_action
                 set_thread_state_valid_blocked_except sts_st_tcb_at')
      apply (clarsimp simp: conj_ac eq_commute)
      apply (rename_tac recvr q recv_state)
      apply (rule_tac Q="\<lambda>_. valid_sched and scheduler_act_not thread and not_queued thread
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
           wp_once hoare_vcg_all_lift)+
  apply (subst st_tcb_at_kh_simp[symmetric])
  apply (clarsimp simp: st_tcb_at_kh_if_split pred_tcb_at_def2 obj_at_def a_type_def
                        valid_sched_def valid_sched_action_def
                        weak_valid_sched_action_def scheduler_act_not_def
                  split: kernel_object.splits)+
    apply (rename_tac tcb recvr q rtcb ep)
    apply (case_tac "recvr = idle_thread s")
     subgoal by (fastforce dest: invs_valid_idle simp: valid_idle_def pred_tcb_at_def obj_at_def)
    apply (case_tac "recvr = cur_thread s")
     subgoal by (fastforce simp: ct_in_state_def st_tcb_at_def2 obj_at_def)
    apply (clarsimp simp: is_activatable_def)
  done*) sorry
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
       not_queued tptr and (ct_active or ct_idle) and invs and (\<lambda>_. valid_fault fault)\<rbrace>
     send_fault_ipc tptr handler_cap fault can_donate
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (simp add: send_fault_ipc_def Let_def)
  apply (case_tac handler_cap; wpsimp)
  apply (wp send_ipc_valid_sched thread_set_not_state_valid_sched thread_set_no_change_tcb_state
      hoare_gen_asm'[OF thread_set_tcb_fault_set_invs]  hoare_drop_imps hoare_vcg_all_lift_R
      ct_in_state_thread_state_lift thread_set_no_change_tcb_state
      hoare_vcg_disj_lift
      | wpc | simp | wps)+
  done
end

lemma handle_no_fault_valid_queues:
  "\<lbrace>valid_queues and not_queued tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: handle_no_fault_def set_thread_state_def)
  apply (wp | simp add:   set_object_def)+
  apply (fastforce simp: valid_queues_def st_tcb_at_kh_if_split not_queued_def)
  done

lemma handle_no_fault_valid_sched_action:
  "\<lbrace>valid_sched_action and scheduler_act_not tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  by (wpsimp simp: handle_no_fault_def wp: set_thread_state_sched_act_not_valid_sched_action)

lemma handle_no_fault_valid_sched:
  "\<lbrace>valid_sched and not_queued tptr and scheduler_act_not tptr\<rbrace>
     handle_no_fault tptr
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  including no_pre
  apply (wp handle_no_fault_valid_queues handle_no_fault_valid_sched_action
            set_thread_state_not_runnable_valid_blocked
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
  "\<lbrace>not_queued t\<rbrace> send_fault_ipc tptr handler_cap fault can_donate -, \<lbrace>\<lambda>rv. not_queued t\<rbrace>"
  by (simp add: send_fault_ipc_def Let_def |
      (wp hoare_drop_imps hoare_vcg_all_lift_R)+ | wpc)+

context DetSchedSchedule_AI begin
lemma handle_fault_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and not_queued thread and (ct_active or ct_idle)
      and scheduler_act_not thread and invs and (\<lambda>_. valid_fault ex)\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_fault_def unless_def
  apply (wpsimp wp: handle_no_fault_valid_sched send_fault_ipc_valid_sched hoare_vcg_if_lift2
hoare_drop_imps hoare_vcg_conj_lift)
sorry

end

lemma idle_not_queued'':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s); queue \<times> {rt} \<subseteq> state_refs_of s ptr\<rbrakk> \<Longrightarrow>
     idle_thread s \<notin> queue"
(*  by (frule idle_only_sc_refs, fastforce simp: valid_idle_def sym_refs_def)*) sorry

context DetSchedSchedule_AI begin

lemma send_signal_valid_sched[wp]:
  "\<lbrace> valid_sched and invs \<rbrace> send_signal ntfnptr badge \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: send_signal_def)
  apply (wp get_simple_ko_wp possible_switch_to_valid_sched'
            set_thread_state_runnable_valid_queues set_thread_state_runnable_valid_sched_action
            set_thread_state_valid_blocked_except sts_st_tcb_at' gts_wp  | wpc | clarsimp)+
       apply (rename_tac ntfn a st)
       apply (rule_tac Q="\<lambda>rv s. valid_sched s \<and> a \<noteq> idle_thread s \<and> not_cur_thread a s" in hoare_strengthen_post)
        apply (wp gts_wp get_simple_ko_wp | simp add: valid_sched_def)+
(*  apply (clarsimp)
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
  done*) sorry

crunch valid_sched[wp]: complete_signal,reply_push valid_sched
  (ignore: resetTimer ackInterrupt wp: gts_wp hoare_drop_imps
   simp: op_equal pred_tcb_weakenE hoare_if_r_and)

lemma receive_ipc_valid_sched:
  "\<lbrace>valid_sched and st_tcb_at active thread and ct_active
          and not_queued thread and scheduler_act_not thread and invs\<rbrace>
   receive_ipc thread cap is_blocking reply_cap
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: receive_ipc_def)
  including no_pre
  apply (wp | wpc | simp add: get_sk_obj_ref_def update_sk_obj_ref_def)+
        apply (wp set_thread_state_sched_act_not_valid_sched | wpc)+
                 apply ((wp set_thread_state_sched_act_not_valid_sched
                        | simp add: do_nbrecv_failed_transfer_def)+)[2]
  (*             apply ((wp possible_switch_to_valid_sched' sts_st_tcb_at' hoare_drop_imps
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
  done*) sorry

end

lemma receive_signal_valid_sched:
  "\<lbrace>valid_sched (*and
 (scheduler_act_not param_a and not_queued param_a and
  valid_etcbs and
  valid_queues and
  weak_valid_sched_action and
  valid_blocked and
  valid_idle_etcb)*)\<rbrace>
receive_signal param_a param_b param_c \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  sorry (* check the preconditions *)
(*
crunch valid_sched: schedule_tcb,maybe_return_sc,maybe_donate_sc valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv)

crunch valid_sched: receive_signal valid_sched
  (wp: set_thread_state_sched_act_not_valid_sched maybeM_inv mapM_wp)
*)

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
  apply (clarsimp simp: reschedule_required_def set_scheduler_action_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc scheduler_act_not_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rename_tac thread inq schedulable)
  apply (wpsimp wp: tcb_sched_action_enqueue_not_queued)
  done

crunch sched_act_not[wp]: tcb_sched_action "scheduler_act_not t"

crunches  set_thread_state,reply_unlink_sc,reply_unlink_tcb
for not_queued[wp]: "not_queued t"
and scheduler_act_not[wp]: "scheduler_act_not t"
 (wp: hoare_drop_imp)

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
       apply (wp tcb_sched_action_enqueue_not_queued | clarsimp | wpc)+
apply (wpsimp wp: hoare_drop_imp)
(*      apply (erule notE, assumption)
     apply (wp reschedule_required_not_queued | simp add: get_ep_queue_def)+
     apply (rule hoare_gen_asm)
     apply (rule_tac S="set queue - {t}" in mapM_x_wp)
      apply (wp tcb_sched_action_enqueue_not_queued | clarsimp)+
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
  done*) sorry
end

crunch not_queued[wp]: set_simple_ko "not_queued t"
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
(*  apply (wp hoare_vcg_imp_lift
         | simp add: get_simple_ko_def get_object_def a_type_def split: kernel_object.splits
         | wpc | wp_once hoare_vcg_all_lift)+
   apply safe
  apply (rename_tac ep x y)
  apply (drule_tac P="\<lambda>ts. \<not> active ts" and ep=ep in
         ntfn_queued_st_tcb_at[rotated, rotated])
  apply (simp_all only: st_tcb_at_not)
  apply (fastforce simp: obj_at_def)+
  done*) sorry

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
  "\<lbrace>valid_objs\<rbrace>
   sched_context_maybe_unbind_ntfn ntfn_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: sched_context_maybe_unbind_ntfn_def get_sk_obj_ref_def
         wp: get_simple_ko_wp)

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
  apply (clarsimp simp: sched_context_maybe_unbind_ntfn_def get_sk_obj_ref_def maybeM_def)
   by (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)

crunches unbind_maybe_notification, unbind_notification,sched_context_maybe_unbind_ntfn,reply_unlink_sc
for  not_queued[wp]: "not_queued t"
and  scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: crunch_wps maybeM_inv)

crunches blocked_cancel_ipc,cancel_signal
for not_queued[wp]: "not_queued t"
and  scheduler_act_not[wp]: "scheduler_act_not t"
  (wp: hoare_drop_imp)

crunches test_reschedule
for not_queued[wp]: "not_queued t"
  (wp: hoare_vcg_if_lift2)

lemma sched_context_donate_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def get_sc_obj_ref_def)
  apply (wpsimp simp: wp: get_sched_context_wp tcb_dequeue_not_queued_gen)
  done

lemma reply_remove_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> reply_remove rptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: reply_remove_def assert_opt_def liftM_def get_tcb_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp)
  apply (case_tac "reply_sc reply"; clarsimp)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (wpsimp simp: wp: hoare_vcg_if_lift2)
    apply (rule_tac Q="\<lambda>_. not_queued t and scheduler_act_not t" in hoare_strengthen_post)
  by wpsimp+

crunch not_queued[wp]: reply_remove_tcb "not_queued t"

lemma reply_cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> reply_cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (wpsimp simp: reply_cancel_ipc_def)

lemma cancel_ipc_not_queued[wp]:
  "\<lbrace>not_queued t and scheduler_act_not t\<rbrace> cancel_ipc tptr \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; wpsimp)
  done

crunch not_queued[wp]: sched_context_unbind_yield_from,sched_context_clear_replies "not_queued t"
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
  "\<lbrace>not_queued t and (st_tcb_at active t and valid_objs and scheduler_act_not t and
    sym_refs \<circ> state_refs_of)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  by (cases cap;
      wpsimp wp: cancel_all_ipc_not_queued cancel_all_signals_not_queued
                 unbind_maybe_notification_valid_objs hoare_vcg_if_lift2 hoare_drop_imp)

end

lemma set_simple_ko_ct_active:
  "\<lbrace>ct_active\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def | wp get_object_wp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def
                  split: kernel_object.splits)
  done

crunch is_etcb_at_ext[wp]: tcb_sched_action, reschedule_required, empty_slot_ext "is_etcb_at t"

crunch is_etcb_at[wp]: reply_remove "is_etcb_at t"
  (wp: hoare_drop_imp)

crunch is_etcb_at[wp]: cancel_ipc "is_etcb_at t"
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
   check_cap_at new_cap src_slot (check_cap_at t slot (cap_insert new_cap src_slot x))
  \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (wp get_cap_wp | simp)+
  done

lemma opt_update_thread_valid_sched[wp]:
  "(\<And>x a. tcb_state (fn a x) = tcb_state x) \<Longrightarrow>
   (\<And>x a. tcb_sched_context (fn a x) = tcb_sched_context x) \<Longrightarrow>
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

crunch valid_sched[wp]: lookup_cap valid_sched

lemma test:
"invs s \<longrightarrow> (\<exists>y. get_tcb thread s = Some y) \<longrightarrow> s \<turnstile> tcb_ctable (the (get_tcb thread s))"
apply (simp add: invs_valid_tcb_ctable_strengthen)
done

context DetSchedSchedule_AI begin

lemma handle_recv_valid_sched:
  "\<lbrace>valid_sched and invs and ct_active
      and ct_not_queued and scheduler_act_sane\<rbrace>
   handle_recv is_blocking can_reply \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
              cong: if_cong split del: if_split)
  apply (wp get_simple_ko_wp handle_fault_valid_sched
            receive_ipc_valid_sched receive_signal_valid_sched | simp)+
     apply (rule hoare_vcg_E_elim)
(*      apply (wpsimp simp: lookup_cap_def lookup_slot_for_thread_def)
       apply (wp resolve_address_bits_valid_fault2)+
    apply (simp add: valid_fault_def)
    apply (wp hoare_drop_imps hoare_vcg_all_lift_R)
   apply (wpsimp wp: delete_caller_cap_not_queued | strengthen invs_valid_tcb_ctable_strengthen)+
  apply (auto simp: ct_in_state_def tcb_at_invs objs_valid_tcb_ctable invs_valid_objs)
  done*) sorry

lemma handle_recv_valid_sched':
  "\<lbrace>invs and valid_sched and ct_active and ct_not_queued and scheduler_act_sane\<rbrace>
    handle_recv is_blocking can_reply
   \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (wp handle_recv_valid_sched)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  done

crunch valid_sched[wp]: reply_from_kernel valid_sched

end

crunch etcb_at[wp]: cap_insert "\<lambda>s. etcb_at P t s"
  (wp: crunch_wps simp: cap_insert_ext_def)

context DetSchedSchedule_AI begin
crunch valid_sched[wp]: invoke_irq_control "valid_sched"
  (wp: maybeM_inv)

lemma fast_finalise_valid_sched[wp]:
  "\<lbrace>valid_sched \<rbrace> fast_finalise cap b \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
sorry(*  by (cases cap; wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp get_simple_ko_inv)

crunch valid_sched[wp]: fast_finalise valid_sched

lemma cap_delete_one_valid_sched[wp]:
  "\<lbrace>valid_sched \<rbrace> cap_delete_one slot \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (clarsimp simp: cap_delete_one_def)
  apply (wpsimp simp: unless_def hoare_vcg_if_lift2 wp: get_cap_wp)
  done

*)

crunch valid_sched[wp]: cap_delete_one valid_sched
  (simp: unless_def wp: maybeM_inv hoare_vcg_if_lift2 hoare_drop_imp
   ignore: fast_finalise)

crunch valid_sched[wp]: cap_delete_one "valid_sched"
  (wp: maybeM_inv simp: unless_def ignore: fast_finalise)

lemma invoke_irq_handler_valid_sched[wp]:
  "\<lbrace> valid_sched \<rbrace> invoke_irq_handler i \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  by (cases i; wpsimp)

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
  apply wp
   apply (simp add: set_domain_def thread_set_domain_def)
   apply (wp gts_st_tcb_at hoare_vcg_if_lift hoare_vcg_if_lift2 hoare_vcg_imp_lift
             hoare_vcg_disj_lift ethread_set_not_queued_valid_queues reschedule_required_valid_sched
             tcb_sched_action_enqueue_valid_blocked ethread_set_valid_blocked_except
             ethread_set_valid_blocked ethread_set_ssa_valid_sched_action
             ethread_set_not_cur_ct_in_cur_domain ethread_set_not_idle_valid_sched
             ethread_set_not_idle_valid_idle_etcb)
      apply (wp static_imp_wp static_imp_conj_wp tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except)
     apply simp
     apply (wp hoare_vcg_disj_lift)
     apply (rule_tac Q="\<lambda>_. valid_sched and not_queued t and valid_idle and (\<lambda>s. t \<noteq> idle_thread s)" in hoare_strengthen_post)
      apply (wp tcb_sched_action_dequeue_valid_sched_not_runnable tcb_dequeue_not_queued)
     apply (simp add: valid_sched_def valid_sched_action_def)
    apply simp
    apply (wp hoare_vcg_disj_lift tcb_dequeue_not_queued tcb_sched_action_dequeue_valid_blocked_except
              tcb_sched_action_dequeue_valid_sched_not_runnable)+
  apply (clarsimp simp: valid_sched_def not_cur_thread_def valid_sched_action_def not_pred_tcb)
  apply (auto simp: st_tcb_def2 tcb_at_def)
  done
(*
lemma idle_not_reply_cap:
  "\<lbrakk> valid_idle s; cte_wp_at ((=) (ReplyCap r)) p s \<rbrakk> \<Longrightarrow> r \<noteq> idle_thread s"
  apply (drule_tac p=p in valid_reply_caps_of_stateD)
   apply (simp add: caps_of_state_def cte_wp_at_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done*)

context DetSchedSchedule_AI begin
lemma perform_invocation_valid_sched[wp]:
  "\<lbrace>invs and valid_invocation i and ct_active and simple_sched_action and valid_sched
         and (\<lambda>s. not_queued (cur_thread s) s)\<rbrace>
     perform_invocation block call can_donate i
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases i, simp_all)
          apply (wp invoke_untyped_valid_sched send_ipc_valid_sched | clarsimp)+
(*         apply (clarsimp simp: ct_in_state_def)
        apply (wp invoke_cnode_valid_sched send_ipc_valid_sched invoke_domain_valid_sched
             | simp add: invs_valid_objs invs_valid_idle invs_valid_reply_caps
             | clarsimp simp: ct_in_state_def)+
  done*) sorry
end
thm reply_push_def
crunch ct_not_queued[wp]: set_thread_state ct_not_queued (wp: ct_not_queued_lift)

crunch valid_sched[wp]: lookup_cap_and_slot valid_sched

context DetSchedSchedule_AI begin
lemma handle_invocation_valid_sched:
  "\<lbrace>invs and valid_sched and ct_active and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     handle_invocation calling blocking can_donate cptr
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

crunch ct_not_queued[wp]: do_machine_op, cap_insert, set_extra_badge "\<lambda>s. not_queued (cur_thread s) s"
  (wp: hoare_drop_imps)

lemma transfer_caps_ct_not_queued[wp]:
  "\<lbrace>\<lambda>s. not_queued (cur_thread s) s\<rbrace>
     transfer_caps info caps ep recv recv_buf
   \<lbrace>\<lambda>rv s. not_queued (cur_thread s) s\<rbrace>"
  by (simp add: transfer_caps_def | wp transfer_caps_loop_pres | wpc)+

crunch ct_sched_act_not[wp]: set_thread_state "\<lambda>s. scheduler_act_not (cur_thread s) s"
  (wp: set_scheduler_action_wp gts_wp hoare_drop_imp
   simp: crunch_simps
   ignore: set_scheduler_action)

context DetSchedSchedule_AI begin

crunch not_queued[wp]: handle_fault_reply "not_queued t"

crunch sched_act_not[wp]: handle_fault_reply "scheduler_act_not t"

crunch valid_etcbs[wp]: set_extra_badge, do_ipc_transfer valid_etcbs
  (wp: crunch_wps const_on_failure_wp simp: crunch_simps
   rule: transfer_caps_loop_pres)

crunch cur[wp]: handle_fault_reply "cur_tcb :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

crunch weak_valid_sched_action[wp]: empty_slot_ext weak_valid_sched_action
  (wp: crunch_wps set_thread_state_runnable_weak_valid_sched_action
       set_bound_notification_weak_valid_sched_action
   simp: cur_tcb_def unless_def)


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
lemma do_reply_transfer_not_queued[wp]:
  "\<lbrace>not_queued t and invs and st_tcb_at active t and scheduler_act_not t and
    K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. not_queued t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc |
         clarsimp split del: if_split | wp_once hoare_drop_imps)+
  sorry

lemma do_reply_transfer_schedact_not[wp]:
  "\<lbrace>scheduler_act_not t and K(receiver \<noteq> t)\<rbrace>
     do_reply_transfer sender receiver
   \<lbrace>\<lambda>_. scheduler_act_not t\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wp hoare_vcg_if_lift | wpc | clarsimp split del: if_split |
         wp_once hoare_drop_imps)+
  sorry


crunch valid_sched[wp]: refill_capacity valid_sched
  (ignore: set_object update_sched_context set_refills)

end

lemma assert_false:"\<lbrace>\<lambda>s. \<not> P\<rbrace> assert P \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply wp
  apply simp
  done
thm do_reply_transfer_def(*
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
  done sorry
*)

(*
lemma reschedule_required_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; clarsimp simp: bind_assoc when_def)
    apply (wpsimp simp: set_scheduler_action_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
   apply (wpsimp simp: set_scheduler_action_def tcb_sched_action_def)
     apply simp
   apply (wpsimp simp: set_scheduler_action_def tcb_sched_action_def)
apply (clarsimp simp: is_schedulable_opt_def)
     apply wpsimp
oops*)
(*

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

crunch ct_not_queued[wp]: set_scheduler_action "ct_not_queued"
crunch not_queued[wp]: set_scheduler_action "not_queued t"

lemma reschedule_required_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> reschedule_required \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (rule hoare_pre)
  apply (rule ct_not_queued_lift; wpsimp wp: reschedule_required_not_queued)
  apply (clarsimp simp: not_queued_def scheduler_act_not_def)
  done

lemma test_reschedule_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace>
     test_reschedule tptr \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  by (wpsimp simp: test_reschedule_def wp: reschedule_required_not_queued)

lemma sched_context_donate_ct_not_queued[wp]:
  "\<lbrace>ct_not_queued and scheduler_act_sane\<rbrace> sched_context_donate sc_ptr tptr \<lbrace>\<lambda>_. ct_not_queued\<rbrace>"
  apply (clarsimp simp: sched_context_donate_def)
  apply (wpsimp simp: set_tcb_obj_ref_def set_sc_obj_ref_def update_sched_context_def
       tcb_sched_action_def get_sc_obj_ref_def
          wp: hoare_drop_imp hoare_vcg_if_lift2 get_sched_context_wp)
  apply (clarsimp simp: etcb_at_def not_queued_def tcb_sched_dequeue_def split: option.splits)
  done

crunch ct_not_queud[wp]: reply_unlink_tcb,reply_unlink_sc ct_not_queued
  (simp: a_type_def wp: hoare_drop_imp)

lemma reply_remove_ct_not_queued[wp]:
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
sorry

lemma reschedule_required_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def)

lemma test_reschedule_scheduler_act_sane[wp]:
  "\<lbrace>scheduler_act_sane\<rbrace> test_reschedule tptr \<lbrace>\<lambda>_. scheduler_act_sane\<rbrace>"
  apply (clarsimp simp: test_reschedule_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; wpsimp)
  done


crunch scheduler_act_sane[wp]: sched_context_donate "scheduler_act_sane"
  (wp: get_object_wp hoare_drop_imp ignore: test_reschedule)

crunch scheduler_act_sane[wp]: reply_remove "scheduler_act_sane"
  (wp: get_object_wp hoare_drop_imp ignore: test_reschedule)

crunch cur_thread[wp]: test_reschedule,tcb_release_enqueue "\<lambda>s. P (cur_thread s)"

crunch cur_thread[wp]: postpone  "\<lambda>s. P (cur_thread s)"
  (wp: dxo_wp_weak hoare_drop_imp ignore: tcb_release_enqueue tcb_sched_action)

crunch cur_thread[wp]: sched_context_donate  "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps maybeM_inv dxo_wp_weak simp: unless_def crunch_simps
   ignore: test_reschedule tcb_sched_action)

context DetSchedSchedule_AI begin

crunch ct_not_queued[wp]: do_ipc_transfer,handle_fault_reply "ct_not_queued"
  (wp: mapM_wp' simp: zipWithM_x_mapM)

lemma do_reply_transfer_ct_not_queued[wp]:
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
  done


crunch cur_thread[wp]: do_reply_transfer "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps maybeM_inv transfer_caps_loop_pres simp: unless_def crunch_simps
   ignore: test_reschedule tcb_sched_action tcb_release_enqueue)


lemma do_reply_transfer_scheduler_act_sane[wp]:
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
done*) sorry

end

locale DetSchedSchedule_AI_handle_hypervisor_fault = DetSchedSchedule_AI +
  assumes handle_hyp_fault_valid_sched[wp]:
    "\<And>t fault.
      \<lbrace>valid_sched and invs and st_tcb_at active t and not_queued t and scheduler_act_not t
          and (ct_active or ct_idle)\<rbrace>
        handle_hypervisor_fault t fault
      \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  assumes handle_reserved_irq_valid_sched' [wp]:
    "\<And>irq.
      \<lbrace>valid_sched and invs and
         (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
        handle_reserved_irq irq
      \<lbrace>\<lambda>rv. valid_sched\<rbrace>"

context DetSchedSchedule_AI_handle_hypervisor_fault begin

lemma handle_interrupt_valid_sched[wp]:
  "\<lbrace>valid_sched and invs and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)\<rbrace>
  handle_interrupt irq \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding handle_interrupt_def
  by (wpsimp wp: get_cap_wp hoare_drop_imps hoare_vcg_all_lift|rule conjI)+

lemma set_scheduler_action_switch_not_cur_thread [wp]:
  "\<lbrace>\<lambda>s. True\<rbrace> set_scheduler_action (switch_thread target) \<lbrace>\<lambda>rv. not_cur_thread t\<rbrace>"
  unfolding set_scheduler_action_def
  by wp (simp add: not_cur_thread_def)

lemma possible_switch_to_not_cur_thread [wp]:
  "\<lbrace>not_cur_thread t\<rbrace> possible_switch_to target \<lbrace>\<lambda>_. not_cur_thread t\<rbrace>"
  unfolding possible_switch_to_def get_tcb_obj_ref_def
  by (rule hoare_seq_ext[OF _ thread_get_sp]) wpsimp

crunch not_ct[wp]: handle_fault,lookup_reply,lookup_cap,receive_ipc,receive_signal "not_cur_thread target"
  (wp: mapM_wp' maybeM_inv hoare_drop_imp hoare_vcg_if_lift2 simp: unless_def)

lemma handle_recv_not_cur_thread[wp]:
  "\<lbrace>not_cur_thread target\<rbrace> handle_recv param_a param_b \<lbrace>\<lambda>_. not_cur_thread target\<rbrace>"
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

crunches refill_budget_check
for ct_active[wp]: ct_active

lemma refill_budget_check_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> refill_budget_check sc_ptr usage capacity \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def refill_full_def)
  by(wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps
         simp: set_refills_def split_del: if_split)

crunches handle_timeout
for valid_sched[wp]: valid_sched


lemma end_timeslice_valid_sched[wp]:
  notes postpone_inv[wp del]  (* need to associate cur_sc to cur_thread *)
  shows
  "\<lbrace>valid_sched\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: end_timeslice_def)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)
  sorry

lemma end_timeslice_ct_active[wp]:
  notes postpone_inv[wp del]  (* need to associate cur_sc to cur_thread *)
  shows
  "\<lbrace>ct_active\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_. ct_active\<rbrace>"
  apply (clarsimp simp: end_timeslice_def)
  apply wpsimp
  sorry

lemma charge_budget_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: charge_budget_def)
  by (wpsimp wp: reschedule_preserves_valid_shed simp: Let_def)

lemma charge_budget_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_. ct_active\<rbrace>"
  by (wpsimp simp: charge_budget_def Let_def)

lemma check_budget_valid_sched[wp]:
  "\<lbrace>valid_sched\<rbrace> check_budget \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  apply (wpsimp wp: reschedule_required_valid_sched get_sched_context_wp
                    hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift)
  apply (clarsimp simp: valid_sched_def valid_sched_action_def)
  done

lemma check_budget_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> check_budget \<lbrace>\<lambda>_. ct_active\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  by (wpsimp wp: hoare_vcg_if_lift2 get_sched_context_wp hoare_vcg_all_lift hoare_drop_imp)

lemma check_budget_restart_valid_sched[wp]:
  "\<lbrace>valid_sched and ct_active\<rbrace> check_budget_restart \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  by (wpsimp simp: check_budget_restart_def
        wp: hoare_vcg_if_lift2 set_thread_state_Restart_valid_sched hoare_drop_imp)

lemma check_budget_restart_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> check_budget_restart \<lbrace>\<lambda>_. ct_active\<rbrace>"
  by (wpsimp simp: check_budget_restart_def set_thread_state_def set_object_def
                 wp: hoare_drop_imp hoare_vcg_if_lift2
        | rule hoare_strengthen_post[where Q="\<lambda>_. ct_active"]
        | simp add: ct_in_state_def pred_tcb_at_def obj_at_def)+

crunches send_ipc,check_budget,check_budget_restart
for simple_sched_action[wp]: simple_sched_action
  (wp: maybeM_inv hoare_drop_imp mapM_wp' simp: Let_def)

(* FIXME: copied from ArchVSpaceEntries_AI, but this should be in the generic context *)
lemma check_budget_restart_invs:
  "\<lbrace>invs\<rbrace> check_budget_restart \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (rule hoare_seq_ext[rotated])
  apply (rule check_budget_invs)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac st; wpsimp)
  by (drule invs_iflive,
       clarsimp simp: if_live_then_nonz_cap_def pred_tcb_at_def obj_at_def live_def)+

crunches update_time_stamp
for valid_sched[wp]: valid_sched
and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
and simple_sched_action[wp]: simple_sched_action

lemma handle_event_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (cases e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def handle_call_def)

apply (wpsimp wp: hoare_whenE_wp handle_invocation_valid_sched hoare_vcg_if_lift2 hoare_drop_imp
ARM.check_budget_restart_invs
| clarsimp simp: invs_valid_objs invs_sym_refs valid_sched_ct_not_queued cong: conj_cong)+
(*            apply ((rule hoare_pre, wp handle_invocation_valid_sched handle_recv_valid_sched'
              | fastforce simp: invs_valid_objs invs_sym_refs valid_sched_ct_not_queued)+)[5]
       apply (wp handle_fault_valid_sched hvmf_active hoare_drop_imps hoare_vcg_disj_lift
                 handle_recv_valid_sched' hoare_vcg_all_lift|
              wpc |
              clarsimp simp: ct_in_state_def valid_sched_ct_not_queued |
              fastforce simp: valid_fault_def)+*)
  sorry

crunch valid_list[wp]: activate_thread valid_list (wp: hoare_drop_imp)
crunch valid_list[wp]: guarded_switch_to, switch_to_idle_thread, choose_thread valid_list
  (wp: crunch_wps)

end

crunch valid_list[wp]: next_domain valid_list (simp: Let_def)
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
                  del: ethread_get_wp
         | wpc | simp)+
  done

lemma call_kernel_valid_list[wp]: "\<lbrace>valid_list\<rbrace> call_kernel e \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: call_kernel_def)
  by (wp | simp)+

lemma call_kernel_valid_sched_helper:
        "\<lbrace> \<lambda>s. (valid_sched and invs and
                            (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow>
                                 scheduler_act_sane s \<and> ct_not_queued s))
                            s \<and>
                           invs s \<rbrace> check_budget \<lbrace>\<lambda>_. \<lambda>s. (valid_sched and invs and
                            (\<lambda>s. the irq \<in> non_kernel_IRQs \<longrightarrow>
                                  scheduler_act_sane s \<and> ct_not_queued s))
                            s \<and>
                           invs s \<rbrace>"
  apply (clarsimp simp: check_budget_def ARM.non_kernel_IRQs_def) (* FIXME RT *) 
  by (wpsimp wp: hoare_vcg_conj_lift reschedule_preserves_valid_shed get_sched_context_wp
                 hoare_drop_imps hoare_vcg_all_lift charge_budget_invs)

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
    apply (wp call_kernel_valid_sched_helper)
    apply (rule hoare_strengthen_post
           [where Q="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> valid_sched s \<and> invs s"])
     apply (wpsimp wp: getActiveIRQ_neq_non_kernel)
    apply auto[1]
   apply (rule_tac Q="\<lambda>rv. valid_sched and invs" and
                   E="\<lambda>rv. valid_sched and invs" in hoare_post_impErr)
     apply (rule valid_validE)
     apply (wp handle_event_valid_sched)
    apply (force intro: active_from_running)+
  done

end

end
