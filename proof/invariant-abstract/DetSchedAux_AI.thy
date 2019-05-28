(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DetSchedAux_AI
imports DetSchedInvs_AI
begin

context begin interpretation Arch .
requalify_facts
  invoke_untyped_st_tcb_at
end

crunches update_cdt_list, create_cap, cap_insert
  for rqueues[wp]: "\<lambda>s::det_state. P (ready_queues s)"
  and schedact[wp]: "\<lambda>s::det_state. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
  and release_queue[wp]: "\<lambda>s::det_state. P (release_queue s)"
  and ct[wp]: "\<lambda>s::det_state. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak)

lemma set_cap_etcbs[wp]:
  "set_cap p c \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto simp: obj_at_def etcbs_of'_def etcb_of_def elim!: rsubst[where P=P])
  done

crunch etcbs[wp]: create_cap, cap_insert "\<lambda>s::det_state. P (etcbs_of s)"
  (wp: dxo_wp_weak crunch_wps)

lemma test_sc_refill_max_cdt_update[simp]:
  "test_sc_refill_max t (s\<lparr>cdt := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma test_sc_refill_max_cdt_list_update[simp]:
  "test_sc_refill_max t (s\<lparr>cdt_list := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma test_sc_refill_max_is_original_cap_update[simp]:
  "test_sc_refill_max t (s\<lparr>is_original_cap := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_cdt_update[simp]:
  "active_sc_tcb_at t (s\<lparr>cdt := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma active_sc_tcb_at_cdt_list_update[simp]:
  "active_sc_tcb_at t (s\<lparr>cdt_list := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma active_sc_tcb_at_is_original_cap_update[simp]:
  "active_sc_tcb_at t (s\<lparr>is_original_cap := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma is_refill_sufficient_cdt_update[simp]:
  "is_refill_sufficient t u (s\<lparr>cdt := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_sufficient_cdt_list_update[simp]:
  "is_refill_sufficient t u (s\<lparr>cdt_list := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_sufficient_is_original_cap_update[simp]:
  "is_refill_sufficient t u (s\<lparr>is_original_cap := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_cdt_update[simp]:
  "is_refill_ready t (s\<lparr>cdt := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_ready_cdt_list_update[simp]:
  "is_refill_ready t (s\<lparr>cdt_list := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_ready_is_original_cap_update[simp]:
  "is_refill_ready t (s\<lparr>is_original_cap := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma test_sc_refill_max_scheduler_action_update[simp]:
  "test_sc_refill_max t (s\<lparr>scheduler_action := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_scheduler_action_update[simp]:
  "active_sc_tcb_at t (s\<lparr>scheduler_action := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_ready_queues_update[simp]:
  "test_sc_refill_max t (s\<lparr>ready_queues := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_ready_queues_update[simp]:
  "active_sc_tcb_at t (s\<lparr>ready_queues := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_release_queue_update[simp]:
  "test_sc_refill_max t (s\<lparr>release_queue := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_release_queue_update[simp]:
  "active_sc_tcb_at t (s\<lparr>release_queue := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_reprogram_timer_update[simp]:
  "test_sc_refill_max t (s\<lparr>reprogram_timer := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_reprogram_timer_update[simp]:
  "active_sc_tcb_at t (s\<lparr>reprogram_timer := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_arch_state_update[simp]:
  "test_sc_refill_max t (s\<lparr>arch_state := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_arch_state_update[simp]:
  "active_sc_tcb_at t (s\<lparr>arch_state := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_consumed_time_update[simp]:
  "test_sc_refill_max t (s\<lparr>consumed_time := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_consumed_time_update[simp]:
  "active_sc_tcb_at t (s\<lparr>consumed_time := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_machine_state_update[simp]:
  "test_sc_refill_max t (s\<lparr>machine_state := param_a\<rparr>) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_machine_state_update[simp]:
  "active_sc_tcb_at t (s\<lparr>machine_state := param_a\<rparr>) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma test_sc_refill_max_trans_state_update[simp]:
  "test_sc_refill_max t (trans_state f s) = test_sc_refill_max t s"
  by (clarsimp simp: test_sc_refill_max_def)

lemma active_sc_tcb_at_trans_state_update[simp]:
  "active_sc_tcb_at t (trans_state f s) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_def)

lemma is_refill_sufficient_scheduler_action_update[simp]:
  "is_refill_sufficient t u (s\<lparr>scheduler_action := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_scheduler_action_update[simp]:
  "is_refill_ready t (s\<lparr>scheduler_action := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_ready_queues_update[simp]:
  "is_refill_sufficient t u (s\<lparr>ready_queues := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_ready_queues_update[simp]:
  "is_refill_ready t (s\<lparr>ready_queues := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_release_queue_update[simp]:
  "is_refill_sufficient t u (s\<lparr>release_queue := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_release_queue_update[simp]:
  "is_refill_ready t (s\<lparr>release_queue := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_reprogram_timer_update[simp]:
  "is_refill_sufficient t u (s\<lparr>reprogram_timer := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_reprogram_timer_update[simp]:
  "is_refill_ready t (s\<lparr>reprogram_timer := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_consumed_time_update[simp]:
  "is_refill_sufficient t u (s\<lparr>consumed_time := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_consumed_time_update[simp]:
  "is_refill_ready t (s\<lparr>consumed_time := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_arch_state_update[simp]:
  "is_refill_sufficient t u (s\<lparr>arch_state := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_arch_state_update[simp]:
  "is_refill_ready t (s\<lparr>arch_state := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma is_refill_sufficient_trans_state_update[simp]:
  "is_refill_sufficient t u (trans_state f s) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_trans_state_update[simp]:
  "is_refill_ready t (trans_state f s) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma tcb_ready_time_is_original_cap_update[simp]:
  "tcb_ready_time t (s\<lparr>is_original_cap := param_a\<rparr>) = tcb_ready_time t s"
  by (fastforce simp: tcb_ready_time_def get_tcb_rev dest!: get_tcb_SomeD split: option.splits)

lemma sorted_release_q_is_original_cap_update[simp]:
  "sorted_release_q (s\<lparr>is_original_cap := param_a\<rparr>) = sorted_release_q s"
  by (clarsimp simp: sorted_release_q_def)

lemma sc_at_period_scheduler_action_update[simp]:
  "sc_at_period P p (s\<lparr>scheduler_action := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_ready_queues_update[simp]:
  "sc_at_period P p (s\<lparr>ready_queues := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_release_queue_update[simp]:
  "sc_at_period P p (s\<lparr>release_queue := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_reprogram_timer_update[simp]:
  "sc_at_period P p (s\<lparr>reprogram_timer := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_consumed_time_update[simp]:
  "sc_at_period P p (s\<lparr>consumed_time := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_arch_state_update[simp]:
  "sc_at_period P p (s\<lparr>arch_state := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_trans_state_update[simp]:
  "sc_at_period P p (trans_state f s) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma sc_at_period_is_original_cap_update[simp]:
  "sc_at_period P p  (s\<lparr>is_original_cap := param_a\<rparr>) = sc_at_period P p s"
  by (clarsimp simp: sc_at_period_def)

lemma set_mrs_active_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace>
     set_mrs r t' mrs \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (wpsimp wp: active_sc_tcb_at_thread_set_no_change)
  apply wp
  done

lemma set_mrs_budget_sufficient [wp]:
  "\<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace>
    set_mrs r t' mrs \<lbrace>\<lambda>rv s::det_state. P (budget_sufficient t s)\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (wpsimp wp: budget_sufficient_thread_set_no_change)
  apply wp
  done

lemma set_mrs_budget_ready [wp]:
  "\<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> set_mrs r t' mrs \<lbrace>\<lambda>rv s::det_state. P (budget_ready t s)\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (wpsimp wp: budget_ready_thread_set_no_change)
  apply wp
  done

lemma set_cap_test_sc_refill_max[wp]:
 "\<lbrace>test_sc_refill_max t\<rbrace> set_cap c p \<lbrace>\<lambda>rv. test_sc_refill_max t\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: test_sc_refill_max_def obj_at_def
       | intro impI conjI | rule_tac x=scp in exI)+
  done

lemma set_cap_active_sc_tcb_at[wp]:
 "\<lbrace>\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)\<rbrace> set_cap c p \<lbrace>\<lambda>rv. \<lambda>s:: det_ext state. P (active_sc_tcb_at t s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def
           elim!: rsubst[where P=P]
       | intro impI conjI iffI | rule_tac x=scp in exI)+
  done

lemma set_cap_is_refill_ready[wp]:
 "\<lbrace>is_refill_ready t\<rbrace> set_cap c p \<lbrace>\<lambda>rv. is_refill_ready t\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: is_refill_ready_def obj_at_def
       | intro impI conjI | rule_tac x=scp in exI)+
  done

lemma set_cap_is_refill_sufficient[wp]:
 "\<lbrace>is_refill_sufficient t u\<rbrace> set_cap c p \<lbrace>\<lambda>rv. is_refill_sufficient t u\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: is_refill_sufficient_def obj_at_def
       | intro impI conjI | rule_tac x=scp in exI)+
  done

lemma set_cap_budget_sufficient[wp]:
 "\<lbrace>\<lambda>s:: det_ext state. P (budget_sufficient t s)\<rbrace> set_cap c p \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wpsimp wp: get_object_wp)
  apply (intro conjI allI impI; clarsimp elim!: rsubst[where P=P];
         clarsimp simp: pred_tcb_at_def obj_at_def is_refill_sufficient_def;
         intro iffI conjI impI; fastforce?)
            apply (clarsimp simp: | rule_tac x=scp in exI)+
  done

lemma set_cap_budget_ready[wp]:
 "\<lbrace>\<lambda>s:: det_ext state. P (budget_ready t s)\<rbrace> set_cap c p \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wpsimp wp: get_object_wp)
  apply (intro conjI allI impI; clarsimp elim!: rsubst[where P=P];
         clarsimp simp: pred_tcb_at_def obj_at_def is_refill_ready_def;
         intro iffI conjI impI; fastforce?)
            apply (clarsimp simp: | rule_tac x=scp in exI)+
  done

lemma set_cap_sorted_release_q[wp]:
 "\<lbrace>valid_release_q\<rbrace> set_cap c p \<lbrace>\<lambda>rv. sorted_release_q\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: valid_release_q_def obj_at_def)
  apply (intro allI impI conjI; clarsimp)
  by (solve_sorted_release_q)+

lemma set_cap_valid_release_q[wp]:
 "\<lbrace>valid_release_q\<rbrace> set_cap c p \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp:  obj_at_def)
  by (intro allI impI conjI; clarsimp, solve_valid_release_q)

crunch_ignore (del: create_cap_ext)

lemma budget_ready_cdt_list_update[simp]:
  "budget_ready t (s\<lparr>cdt_list := param_a\<rparr>) = budget_ready t s"
  by (clarsimp simp: is_refill_ready_def)

lemma budget_sufficient_cdt_list_update[simp]:
  "budget_sufficient t (s\<lparr>cdt_list := param_a\<rparr>) = budget_sufficient t s"
  by (clarsimp simp: is_refill_sufficient_def)

crunches create_cap_ext,cap_insert_ext
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and is_refill_sufficient[wp]: "is_refill_sufficient t u:: det_state \<Rightarrow> bool"
and is_refill_ready[wp]: "is_refill_ready t:: det_state \<Rightarrow> bool"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state. P (budget_ready t s)"
 (simp: crunch_simps wp: hoare_drop_imps valid_ready_qs_lift)

crunches create_cap,cap_insert
for active_sc_tcb_at[wp]: "\<lambda>s:: det_ext state. P (active_sc_tcb_at t s)"
and is_refill_sufficient[wp]: "is_refill_sufficient t u:: det_state \<Rightarrow> bool"
and is_refill_ready[wp]: "is_refill_ready t:: det_state \<Rightarrow> bool"
and budget_sufficient[wp]: "\<lambda>s:: det_ext state. P (budget_sufficient t s)"
and budget_ready[wp]: "\<lambda>s:: det_ext state. P (budget_ready t s)"
 (simp: crunch_simps wp: hoare_drop_imps crunch_wps)

crunches create_cap,cap_insert
for valid_ready_qs[wp]: "valid_ready_qs:: det_state \<Rightarrow> _"
 (simp: crunch_simps wp: hoare_drop_imps valid_ready_qs_lift)

lemma typ_at_pred_tcb_at_lift:
  assumes typ_lift: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at T p s)\<rbrace>"
  assumes pred_lift: "\<And>P. \<lbrace>pred_tcb_at proj P t\<rbrace> f \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace> f \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply clarsimp
  apply (case_tac "kheap s t")
   apply (cut_tac P="\<lambda>x. \<not> x" and p=t and T="ATCB" in typ_lift)
   apply (simp add: valid_def obj_at_def)
   apply force
  apply (cut_tac P="\<lambda>x. x" and p=t and T="a_type aa" in typ_lift)
  apply (cut_tac P="\<lambda>t. \<not> P t" in pred_lift)
  apply (simp add: valid_def obj_at_def pred_tcb_at_def)
  apply (drule_tac x=s in spec)
  apply simp
  apply (drule_tac x="(a,b)" in bspec)
   apply simp
  apply simp
  apply (subgoal_tac "a_type aa = ATCB")
   apply (erule a_type_ATCBE)
   apply simp
   apply force
  apply simp
  done


lemma create_cap_no_pred_tcb_at: "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace>
          create_cap apiobject_type nat' prod' dev x
          \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  by (rule typ_at_pred_tcb_at_lift; wp)

lemma cap_insert_no_pred_tcb_at:
  "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>r s. \<not> pred_tcb_at proj P t s\<rbrace>"
  by (rule typ_at_pred_tcb_at_lift; wp)


locale DetSchedAux_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes invoke_untyped_ct[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::'state_ext state. P (cur_thread s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes invoke_untyped_bound_sc[wp]:
    "\<And>P i t. \<lbrace>\<lambda>s::'state_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and bound_sc_tcb_at P t and ct_active and valid_untyped_inv i
       and (\<lambda>s::'state_ext state. scheduler_action s = resume_cur_thread)) s\<rbrace>
       invoke_untyped i \<lbrace>\<lambda>_ s. bound_sc_tcb_at P t s\<rbrace>"

locale DetSchedAux_AI_det_ext = DetSchedAux_AI "TYPE(det_ext)" +
  assumes delete_objects_etcb_at[wp]:
    "\<And>P t a b. \<lbrace>\<lambda>s::det_ext state. etcb_at P t s\<rbrace> delete_objects a b \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  assumes invoke_untyped_etcb_at:
    "\<And>P t ui.
      \<lbrace>(\<lambda>s :: det_ext state. etcb_at P t s)\<rbrace>
        invoke_untyped ui
      \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace> "
  assumes invoke_untyped_active_sc_tcb_at:
    "\<And>i t. \<lbrace>\<lambda>s :: det_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and active_sc_tcb_at t and ct_active and valid_untyped_inv i
       and (\<lambda>s. scheduler_action s = resume_cur_thread)) s\<rbrace> invoke_untyped i
       \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  assumes invoke_untyped_budget_sufficient:
    "\<And>t i. \<lbrace>\<lambda>s::det_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and (\<lambda>s. (budget_sufficient t s)) and ct_active and valid_untyped_inv i
       and (\<lambda>s. scheduler_action s = resume_cur_thread)) s\<rbrace>
                 invoke_untyped i \<lbrace>\<lambda>_ s. (budget_sufficient t s)\<rbrace>"
  assumes invoke_untyped_budget_ready:
    "\<And>t i. \<lbrace>\<lambda>s::det_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and (\<lambda>s. (budget_ready t s)) and ct_active and valid_untyped_inv i
       and (\<lambda>s. scheduler_action s = resume_cur_thread)) s\<rbrace>
                  invoke_untyped i \<lbrace>\<lambda>_ s. (budget_ready t s)\<rbrace>"
  assumes invoke_untyped_cur_domain[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (cur_domain s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  assumes invoke_untyped_ready_queues[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (ready_queues s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (ready_queues s)\<rbrace>"
  assumes invoke_untyped_scheduler_action[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (scheduler_action s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  assumes invoke_untyped_release_queue[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (release_queue s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (release_queue s)\<rbrace>"
  assumes invoke_untyped_tcb_ready_time[wp]:
    "\<And>P t i. \<lbrace>invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t and
     active_sc_tcb_at t and
    ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread) and
    valid_untyped_inv i and (\<lambda>s::det_ext state. P (tcb_ready_time t s))\<rbrace>
                  invoke_untyped i \<lbrace>\<lambda>_ s. P (tcb_ready_time t s) \<and> active_sc_tcb_at t s\<rbrace>"
    assumes init_arch_objects_valid_blocked[wp]:
    "\<And>t r n sz refs. \<lbrace>valid_blocked::det_ext state \<Rightarrow> _\<rbrace> init_arch_objects t r n sz refs \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes init_arch_objects_valid_machine_time[wp]:
    "\<And>t r n sz refs. init_arch_objects t r n sz refs \<lbrace>valid_machine_time::det_ext state \<Rightarrow> _\<rbrace>"
  assumes init_arch_objects_valid_release_q[wp]:
    "\<And>t r n sz refs. \<lbrace>valid_release_q::det_ext state \<Rightarrow> _\<rbrace> init_arch_objects t r n sz refs \<lbrace>\<lambda>_. valid_release_q\<rbrace>"
  assumes invoke_untyped_idle_thread[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (idle_thread s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"

lemmas mapM_x_defsym = mapM_x_def[symmetric]

crunches update_cdt_list,set_cdt
for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at t ts s)"
and typ_at[wp]: "\<lambda>s. P (typ_at T t s)"
and active_sc_tcb_at'[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"
and sorted_release_q[wp]: sorted_release_q
and valid_release_q[wp]: valid_release_q


crunch valid_blocked[wp]: create_cap, cap_insert, set_cap "valid_blocked::det_state \<Rightarrow> _"
  (wp: crunch_wps valid_blocked_lift set_cap_typ_at hoare_drop_imps simp: crunch_simps)

crunch valid_blocked_except_set[wp]: create_cap, cap_insert, set_cap "valid_blocked_except_set S::det_state \<Rightarrow> _"
  (wp: crunch_wps valid_blocked_except_set_lift set_cap_typ_at hoare_drop_imps simp: crunch_simps)

lemma set_cap_ko_at_Endpoint_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    set_cap param_a param_b
   \<lbrace>\<lambda>_ s. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (fastforce simp: obj_at_def)
  done

lemma set_cdt_list_wp:
  "\<lbrace>\<lambda>s. P (cdt_list_update (\<lambda>_. cdtl) s)\<rbrace> set_cdt_list cdtl \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding set_cdt_list_def
  by wpsimp

lemma create_cap_ext_ko_at_Endpoint_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    create_cap_ext a b c
   \<lbrace>\<lambda>_ s::det_state. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding create_cap_ext_def update_cdt_list_def
  by (wpsimp wp: set_cdt_list_wp)

lemma cap_insert_ext_ko_at_Endpoint_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>_ s::det_state. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding cap_insert_ext_def update_cdt_list_def
  by (wpsimp wp: set_cdt_list_wp)

lemma create_cap_ko_at_Endpoint_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    create_cap type bits untyped is_device param_b
   \<lbrace>\<lambda>_ s::det_state. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding create_cap_def
  by wpsimp

lemma cap_insert_ko_at_Endpoint_at[wp]:
  "\<lbrace>\<lambda>s. Q (ko_at (Endpoint ep) p s)\<rbrace>
    cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_ s::det_state. Q (ko_at (Endpoint ep) p s)\<rbrace>"
  unfolding cap_insert_def
  by (wpsimp wp: hoare_vcg_if_lift2 get_cap_wp simp: set_untyped_cap_as_full_def | safe)+

crunches set_cdt, set_cap, create_cap, cap_insert
  for valid_ep_q[wp]: "valid_ep_q::det_state \<Rightarrow> _"
  (wp: valid_ep_q_lift crunch_wps hoare_vcg_disj_lift simp: crunch_simps)

lemma valid_blocked_fold_update:
  "\<lbrakk> valid_blocked_2 queues rlq kh sa ct; type \<noteq> apiobject_type.Untyped \<rbrakk> \<Longrightarrow>
  valid_blocked_2 queues rlq (foldr (\<lambda>p kh. kh(p \<mapsto> default_object type dev o_bits dm)) ptrs kh) sa ct"
  apply (induct ptrs)
   apply simp
  apply (case_tac type)
        apply (fastforce simp: valid_blocked_def st_tcb_at_kh_def default_sched_context_def
                              default_object_def default_tcb_def active_sc_tcb_at_defs
              split: option.splits if_splits)+
  done

lemma retype_region_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> retype_region a b c d dev \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: retype_region_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (blast intro: valid_blocked_fold_update)
  done

lemma delete_objects_valid_blocked[wp]:
  "\<lbrace>valid_blocked\<rbrace> delete_objects a b \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wpsimp simp: detype_def wrap_ext_det_ext_ext_def do_machine_op_def)
  apply (fastforce simp add: valid_blocked_def st_tcb_at_kh_def
                   is_etcb_at_def active_sc_tcb_at_defs split: option.splits)
  done

crunch valid_blocked[wp]: reset_untyped_cap "valid_blocked::det_state \<Rightarrow> _"
  (wp: preemption_point_inv mapME_x_inv_wp crunch_wps
   simp: unless_def)

context DetSchedAux_AI_det_ext begin

lemma invoke_untyped_valid_blocked[wp]:
  "invoke_untyped ui \<lbrace>valid_blocked :: det_ext state \<Rightarrow> _\<rbrace>"
  unfolding invoke_untyped_def
  supply if_split [split del]
  by (wpsimp wp: crunch_wps mapME_x_inv_wp simp: mapM_x_defsym crunch_simps unless_def)

end

lemma st_tcb_at_is_etcb:
  "st_tcb_at P t s \<Longrightarrow> is_etcb_at' t (etcbs_of s)"
  by (auto simp: etcbs_of'_def is_etcb_at'_def st_tcb_at_def obj_at_def)

(*Leverages the fact that retype only clears out inactive tcbs under
  the invariants*)
lemma valid_sched_tcb_state_preservation:
  assumes st_tcb: "\<And>P t. \<lbrace>I and ct_active and st_tcb_at (P and Not o inactive and Not o idle) t\<rbrace> f \<lbrace>\<lambda>_.st_tcb_at P t\<rbrace>"
  assumes stuff: "\<And>P t. \<lbrace>etcb_at P t\<rbrace> f \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  assumes bound_sc: "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes budget_s: "\<And>t. \<lbrace>\<lambda>s. (budget_sufficient t s)\<rbrace> f \<lbrace>\<lambda>rv s. (budget_sufficient t s)\<rbrace>"
  assumes budget_r: "\<And>t. \<lbrace>\<lambda>s. (budget_ready t s)\<rbrace> f \<lbrace>\<lambda>rv s. (budget_ready t s)\<rbrace>"
      and time': "\<And>P t t'. \<lbrace>\<lambda>a. P (tcb_ready_time t a)(tcb_ready_time t' a) \<rbrace> f
                  \<lbrace>\<lambda>rv a. P (tcb_ready_time t a)(tcb_ready_time t' a)\<rbrace>"
      and time: "\<And>P t. \<lbrace>\<lambda>a. P (tcb_ready_time t a)\<rbrace> f
                  \<lbrace>\<lambda>rv a. P (tcb_ready_time t a)\<rbrace>"
  assumes cur_thread: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes idle_thread: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes valid_blocked: "\<lbrace>valid_blocked\<rbrace> f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes valid_idle: "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes valid_others:
        "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>
            f \<lbrace>\<lambda>r s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>"
  shows "\<lbrace>I and ct_active and valid_sched and valid_idle\<rbrace> f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
proof -
  show ?thesis
  apply (clarsimp simp add: valid_sched_def valid_def)
  apply (frule(1) use_valid[OF _ valid_blocked])
  apply simp
  apply (frule_tac P1="\<lambda>sa rq cdom rlq. rq = ready_queues s \<and> sa = scheduler_action s \<and> cdom = cur_domain s \<and> rlq = release_queue s" in use_valid[OF _ valid_others])
   apply simp
  apply (rule conjI)
   apply (clarsimp simp add: valid_ready_qs_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply clarsimp
   apply (drule_tac x=t in bspec)
    apply simp
   apply clarsimp
   apply (subgoal_tac "st_tcb_at runnable t b \<and> active_sc_tcb_at t b
                          \<and> budget_sufficient t b \<and> budget_ready t b")
    apply simp
    apply (frule_tac P1="\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d" and t1=t in use_valid[OF _ stuff])
     apply simp
    apply (simp add: pred_tcb_at_def obj_at_def)
    apply force
   apply (rule_tac conjI[OF use_valid[OF _ st_tcb]
        conjI[OF use_valid[OF _ bound_sc]
          conjI[OF use_valid[OF _ budget_s] use_valid[OF _ budget_r]]]], assumption)
         apply simp
         apply (erule pred_tcb_weakenE)
         apply simp
         apply (case_tac "itcb_state tcb")
                apply simp+
  apply (frule_tac P1="\<lambda>ct. ct = (cur_thread s)" in use_valid[OF _ cur_thread])
   apply simp
  apply (rule conjI)
   apply (clarsimp simp add: valid_release_q_def)
  apply (rule conjI, clarsimp)
   apply (drule_tac x=t in bspec)
    apply simp
   apply clarsimp
   apply (subgoal_tac "st_tcb_at runnable t b \<and> active_sc_tcb_at t b")
    apply simp
   apply (rule_tac conjI[OF use_valid[OF _ st_tcb] use_valid[OF _ bound_sc]], assumption)
     apply clarsimp
     apply (erule pred_tcb_weakenE)
     apply simp
     apply (case_tac "itcb_state tcb")
               apply (simp+)[10]
     apply (clarsimp simp: sorted_release_q_def elim!: sorted_wrt_mono_rel[rotated])
     apply (frule_tac P1="\<lambda>t t'. t \<le> t'" in use_valid[OF _ release_queue_cmp_lift[OF time]], simp+)
  apply (frule_tac P1="\<lambda>ct. ct = (cur_thread s)" in use_valid[OF _ cur_thread])
   apply simp
  apply (rule conjI)
   apply simp
  apply (clarsimp simp add: valid_sched_action_def is_activatable_def weak_valid_sched_action_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac P1="active" and t1="cur_thread s" in use_valid[OF _ st_tcb])
    apply (simp add: ct_in_state_def)
    apply (erule pred_tcb_weakenE)
    apply simp
    apply (case_tac "itcb_state tcb"; simp)
   apply (erule pred_tcb_weakenE)
   apply (case_tac "itcb_state tcb"; simp)
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply (rule_tac use_valid[OF _ st_tcb],assumption)
   apply simp
  apply (erule pred_tcb_weakenE)
   apply simp
   apply (case_tac "itcb_state tcb", simp+)
      apply (rule conjI)
       apply (rule_tac use_valid[OF _ budget_s],assumption, simp)
      apply (rule conjI)
       apply (rule_tac use_valid[OF _ budget_r],assumption, simp)
      apply (rule_tac use_valid[OF _ bound_sc],assumption)
   apply simp
   apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def)
   apply (rule use_valid[OF _ stuff, rule_format], assumption)
    apply simp
   apply (rule use_valid[OF _ st_tcb], assumption)
   apply simp
   apply (erule st_tcb_weakenE)
   apply (case_tac st, simp+)
  apply (clarsimp simp: ct_in_cur_domain_2_def in_cur_domain_2_def)
  apply (frule_tac P1="\<lambda>idle. idle = (idle_thread s)" in use_valid[OF _ idle_thread], simp)
  apply (rule conjI)
   apply (rule impI)
   apply (simp, erule disjE, simp)
   apply (frule_tac P1="\<lambda>t. etcb_domain t = cur_domain s" and t1="cur_thread s" in use_valid[OF _ stuff])
    apply (clarsimp simp: etcb_at_def split: option.splits)
   apply clarsimp
   apply (erule notE, rule use_valid[OF _ st_tcb],assumption)
   apply (simp add: ct_in_state_def)
   apply (erule st_tcb_weakenE)
   apply simp
   apply (case_tac st, simp+)
  apply(frule (1) use_valid[OF _ valid_idle])
  apply(simp add: valid_idle_etcb_def)
  apply(frule use_valid[OF _ stuff[where t=idle_thread_ptr]])
   apply simp
  apply(erule mp)
  apply(fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done
qed

(*Leverages the fact that retype only clears out inactive tcbs under
  the invariants*)
lemma valid_sched_tcb_state_preservation_gen:
  assumes st_tcb: "\<And>P t. \<lbrace>I and ct_active and st_tcb_at (P and Not o inactive and Not o idle) t\<rbrace> f \<lbrace>\<lambda>_.st_tcb_at P t\<rbrace>"
  assumes stuff: "\<And>P t. \<lbrace>etcb_at P t\<rbrace> f \<lbrace>\<lambda>r s. st_tcb_at (Not o inactive) t s \<longrightarrow> etcb_at P t s\<rbrace>"
  assumes bound_sc:
            "\<And>t. \<lbrace>I and ct_active and st_tcb_at (Not o inactive and Not o idle) t and active_sc_tcb_at t\<rbrace>
                                 f \<lbrace>\<lambda>_.active_sc_tcb_at t\<rbrace>"  (* is this correct? *)
  assumes budget_s: "\<And>t. \<lbrace>I and st_tcb_at (Not o inactive and Not o idle) t
                           and (\<lambda>s. (budget_sufficient t s))\<rbrace> f \<lbrace>\<lambda>r s. (budget_sufficient t s)\<rbrace>"
  assumes budget_r: "\<And>t. \<lbrace>I and st_tcb_at (Not o inactive and Not o idle) t
                           and (\<lambda>s. (budget_ready t s))\<rbrace> f \<lbrace>\<lambda>r s. (budget_ready t s)\<rbrace>"
      and time: "\<And>P t. \<lbrace>(\<lambda>a. P (tcb_ready_time t a))
              and I and st_tcb_at (Not o inactive and Not o idle) t and active_sc_tcb_at t\<rbrace> f \<lbrace>\<lambda>rv a. P (tcb_ready_time t a)\<rbrace>"
  assumes cur_thread: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes idle_thread: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes valid_blocked: "\<lbrace>valid_blocked\<rbrace> f \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes valid_idle: "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  assumes valid_others:
        "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>
            f \<lbrace>\<lambda>r s. P (scheduler_action s) (ready_queues s) (cur_domain s) (release_queue s)\<rbrace>"
  shows "\<lbrace>I and ct_active and valid_sched and valid_idle\<rbrace> f \<lbrace>\<lambda>_. valid_sched\<rbrace>"
proof -
  show ?thesis
    apply (clarsimp simp add: valid_sched_def valid_def)
    apply (frule(1) use_valid[OF _ valid_blocked])
    apply simp
    apply (frule_tac P1="\<lambda>sa rq cdom rlq. rq = ready_queues s \<and> sa = scheduler_action s \<and> cdom = cur_domain s \<and> rlq = release_queue s" in use_valid[OF _ valid_others])
     apply simp
    apply (rule conjI)
    (* valid_ready_qs *)
     apply (clarsimp simp add: valid_ready_qs_def)
     apply (drule_tac x=d in spec)
     apply (drule_tac x=p in spec)
     apply clarsimp
     apply (drule_tac x=t in bspec)
      apply simp
     apply clarsimp
     apply (subgoal_tac "st_tcb_at runnable t b \<and> active_sc_tcb_at t b
                          \<and> budget_sufficient t b \<and> budget_ready t b")
      apply simp
      apply (frule_tac P1="\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d" and t1=t in use_valid[OF _ stuff])
       apply simp
      apply (simp add: pred_tcb_at_def obj_at_def)
      apply force
     apply (rule_tac conjI[OF use_valid[OF _ st_tcb]
          conjI[OF use_valid[OF _ bound_sc]
            conjI[OF use_valid[OF _ budget_s] use_valid[OF _ budget_r]]]], assumption)
           apply simp
           apply ((erule pred_tcb_weakenE, simp, case_tac "itcb_state tcb", simp+)+)[7]
    apply (rule conjI)
      (* valid_release_q *)
     apply (clarsimp simp: valid_release_q_def)
     apply (rule conjI, clarsimp)
      apply (drule_tac x=t in bspec, simp, clarsimp)
      apply (subgoal_tac "st_tcb_at runnable t b \<and> active_sc_tcb_at t b")
       apply simp
      apply (rule_tac conjI[OF use_valid[OF _ st_tcb] use_valid[OF _ bound_sc]], assumption)
        apply simp
        apply ((erule pred_tcb_weakenE, simp, case_tac "itcb_state tcb", simp+)+)[3]
     apply (clarsimp simp: sorted_release_q_def elim!: sorted_wrt_mono_rel[rotated])
     apply (frule_tac x=x in bspec, simp)
     apply (drule_tac x=y in bspec, simp, clarsimp)
     apply (frule_tac P1="\<lambda>t. t \<le> tcb_ready_time y b" and t1=x in use_valid[OF _ time], simp+)
      apply (rule conjI)
       apply (frule_tac P1="\<lambda>t. tcb_ready_time x s \<le> t" and t1=y in use_valid[OF _ time], simp+)
        apply ((erule pred_tcb_weakenE, simp, case_tac "itcb_state tcb", simp+)+)[4]
      (* ct_not_in_q and others *)
    apply (frule_tac P1="\<lambda>ct. ct = (cur_thread s)" in use_valid[OF _ cur_thread])
     apply simp+
    apply (clarsimp simp add: valid_sched_action_def is_activatable_def weak_valid_sched_action_def)
    apply (rule conjI)
     apply clarsimp
     apply (frule_tac P1="active" and t1="cur_thread s" in use_valid[OF _ st_tcb])
      apply (simp add: ct_in_state_def)
      apply (erule pred_tcb_weakenE)
      apply simp
      apply (case_tac "itcb_state tcb"; simp)
     apply (erule pred_tcb_weakenE)
     apply (case_tac "itcb_state tcb"; simp)
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI)
      apply (rule_tac use_valid[OF _ st_tcb],assumption)
      apply simp
      apply (erule pred_tcb_weakenE)
      apply simp
      apply (case_tac "itcb_state tcb", simp+)
     apply (rule conjI)
      apply (rule_tac use_valid[OF _ budget_s],assumption, simp)
      apply (erule pred_tcb_weakenE, fastforce)
     apply (rule conjI)
      apply (rule_tac use_valid[OF _ budget_r],assumption, simp)
      apply (erule pred_tcb_weakenE, fastforce)
     apply (rule_tac use_valid[OF _ bound_sc],assumption)
     apply simp
     apply (erule pred_tcb_weakenE, fastforce)
    apply (rule conjI)
     apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def)
     apply (rule use_valid[OF _ stuff, rule_format], assumption)
      apply simp
     apply (rule use_valid[OF _ st_tcb], assumption)
     apply simp
     apply (erule st_tcb_weakenE)
     apply (case_tac st, simp+)
    apply (clarsimp simp: ct_in_cur_domain_2_def in_cur_domain_2_def)
    apply (frule_tac P1="\<lambda>idle. idle = (idle_thread s)" in use_valid[OF _ idle_thread], simp)
    apply (rule conjI)
     apply (rule impI)
     apply (simp, erule disjE, simp)
     apply (frule_tac P1="\<lambda>t. etcb_domain t = cur_domain s" and t1="cur_thread s" in use_valid[OF _ stuff])
      apply (clarsimp simp: etcb_at_def split: option.splits)
     apply clarsimp
     apply (erule notE, rule use_valid[OF _ st_tcb],assumption)
     apply (simp add: ct_in_state_def)
     apply (erule st_tcb_weakenE)
     apply simp
     apply (case_tac st, simp+)
    apply(frule (1) use_valid[OF _ valid_idle])
    apply(simp add: valid_idle_etcb_def)
    apply(frule use_valid[OF _ stuff[where t=idle_thread_ptr]])
     apply simp
    apply(erule mp)
    apply(fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)
    done
qed

lemma valid_idle_etcb_lift:
  assumes "\<And>P t. \<lbrace>\<lambda>s. etcb_at P t s\<rbrace> f \<lbrace>\<lambda>r s. etcb_at P t s\<rbrace>"
  shows "\<lbrace>valid_idle_etcb\<rbrace> f \<lbrace>\<lambda>r. valid_idle_etcb\<rbrace>"
  apply(simp add: valid_idle_etcb_def)
  apply(wp assms)
  done

(* sorted_release_q lemmas *)
crunches set_thread_state_act
for sorted_release_q[wp]: "sorted_release_q::det_state \<Rightarrow> _"
 (wp: crunch_wps hoare_drop_imp simp: crunch_simps)

lemma set_thread_state_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and not_in_release_q tp and valid_release_q\<rbrace>
      set_thread_state tp st
   \<lbrace>\<lambda>rv. sorted_release_q::det_state \<Rightarrow> _\<rbrace>"
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (clarsimp simp: valid_release_q_def not_in_release_q_def
        split: option.splits dest!: get_tcb_SomeD)
  by solve_sorted_release_q

lemma set_simple_ko_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace> set_simple_ko C ref new
            \<lbrace>\<lambda>_. sorted_release_q\<rbrace> "
  apply (clarsimp simp: set_simple_ko_def)
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (clarsimp simp: partial_inv_def a_type_def split: kernel_object.splits)
  apply (clarsimp simp: valid_release_q_def)
  by (intro conjI impI allI; clarsimp; solve_sorted_release_q)

lemma update_sk_obj_ref_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace> update_sk_obj_ref C f ref new
            \<lbrace>\<lambda>_. sorted_release_q\<rbrace> "
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_sc_replies_sorted_release_q[wp]:
  "\<lbrace>sorted_release_q and valid_release_q\<rbrace>
   set_sc_obj_ref sc_replies_update ref list \<lbrace>\<lambda>_. sorted_release_q\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp simp_del: fun_upd_apply)
  by (clarsimp simp: valid_release_q_def obj_at_def) solve_sorted_release_q

(* FIXME move *)
lemma tcb_ready_time_kh_thread_state_update[simp]:
  "\<lbrakk>active_sc_tcb_at x s; kheap s tp = Some (TCB tcb)\<rbrakk> \<Longrightarrow>
     tcb_ready_time_kh x
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_state := ts\<rparr>)))
        = tcb_ready_time_kh x (kheap s)"
  by (fastforce simp: tcb_ready_time_kh_def active_sc_tcb_at_defs split: option.splits)

(* FIXME move *)
lemma tcb_ready_time_kh_tcb_bn_update[simp]:
  "\<lbrakk>active_sc_tcb_at x s; kheap s tp = Some (TCB tcb)\<rbrakk> \<Longrightarrow>
     tcb_ready_time_kh x
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_bound_notification := ntfn\<rparr>)))
        = tcb_ready_time_kh x (kheap s)"
  by (fastforce simp: tcb_ready_time_kh_def active_sc_tcb_at_defs split: option.splits)

(* FIXME move *)
lemma tcb_ready_time_kh_tcb_arch_update[simp]:
  "\<lbrakk>active_sc_tcb_at x s; kheap s tp = Some (TCB tcb)\<rbrakk> \<Longrightarrow>
     tcb_ready_time_kh x
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_arch := ntfn\<rparr>)))
        = tcb_ready_time_kh x (kheap s)"
  by (fastforce simp: tcb_ready_time_kh_def active_sc_tcb_at_defs split: option.splits)

(* FIXME move *)
lemma tcb_ready_time_kh_tcb_sc_update:
  "\<lbrakk>kheap s tp = Some (TCB tcb);
    tcb_sched_context tcb = Some scp; kheap s scp = Some (SchedContext sc n);
    scopt = Some scp'; kheap s scp' = Some (SchedContext sc' n');
    r_time (refill_hd sc) = r_time (refill_hd sc') \<rbrakk> \<Longrightarrow>
     tcb_ready_time_kh x
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_sched_context := scopt\<rparr>)))
        = tcb_ready_time_kh x (kheap s)"
  by (fastforce simp: tcb_ready_time_kh_def active_sc_tcb_at_defs split: option.splits kernel_object.splits)

lemma tcb_ready_time_kh_tcb_yt_update[simp]:
  "\<lbrakk>active_sc_tcb_at x s; kheap s tp = Some (TCB tcb)\<rbrakk> \<Longrightarrow>
     tcb_ready_time_kh x
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_yield_to := ntfn\<rparr>)))
        = tcb_ready_time_kh x (kheap s)"
  by (fastforce simp: tcb_ready_time_kh_def active_sc_tcb_at_defs split: option.splits)

lemmas tcb_ready_time_kh_update' = tcb_ready_time_kh_thread_state_update[simplified fun_upd_def]
                                   tcb_ready_time_kh_tcb_bn_update[simplified fun_upd_def]
                                   tcb_ready_time_kh_tcb_yt_update[simplified fun_upd_def]
                                   tcb_ready_time_kh_tcb_arch_update[simplified fun_upd_def]
declare tcb_ready_time_kh_update'[simp]

lemma sc_replies_update_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_sc_obj_ref sc_replies_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                  wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

lemma set_simple_ko_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_simple_ko f ptr ep
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def
                  wp: get_object_wp)
  by (safe; clarsimp simp: partial_inv_def a_type_def obj_at_def
                   tcb_ready_time_ep_update[simplified obj_at_def is_ep fun_upd_def]
                   tcb_ready_time_reply_update[simplified obj_at_def is_reply fun_upd_def]
                   tcb_ready_time_ntfn_update[simplified obj_at_def is_ntfn fun_upd_def]
           split: option.splits if_split_asm kernel_object.splits)

crunches store_word_offs,create_cap_ext,set_cdt,do_machine_op,cap_insert_ext
for tcb_ready_time_inv'[wp]: "\<lambda>s. P (tcb_ready_time t s)"

lemma set_cap_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
       set_cap cap slot
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_cap_def set_object_def wp: get_object_wp)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

lemma thread_set_valid_release_ready_time_inv'[wp]:
  "\<lbrakk> \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
    thread_set f tptr
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp simp: set_object_def)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                simp: get_tcb_def tcb_ready_time_def split: option.splits)

lemma set_mrs_tcb_ready_time_inv'[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)\<rbrace>
    set_mrs thread buf msgs
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)\<rbrace>"
  apply (wpsimp simp: set_mrs_def set_object_def zipWithM_x_mapM wp: mapM_wp' get_object_wp
                split_del: if_split)
  by (fastforce simp: tcb_ready_time_def active_sc_tcb_at_defs get_tcb_def
                dest!: get_tcb_SomeD split: option.splits)

crunches set_simple_ko, set_cap, set_mrs,create_cap_ext
for tcb_ready_time_inv[wp]: "\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)"
  (rule: release_queue_cmp_lift)

lemma sc_replies_update_tcb_ready_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>
       set_sc_obj_ref sc_replies_update scptr new
       \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>"
  by (rule hoare_lift_Pf3[where f="\<lambda>s. tcb_ready_time t' s"]; wpsimp)

lemma thread_set_valid_release_ready_time_inv[wp]:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>
    thread_set f tptr
   \<lbrace>\<lambda>_ s. P (tcb_ready_time t s)(tcb_ready_time t' s)\<rbrace>"
  by (rule release_queue_cmp_lift; wpsimp)

crunches cap_insert
for tcb_ready_time_inv'[wp]: "\<lambda>s::det_state. P (tcb_ready_time t s)"
  (wp: crunch_wps simp: crunch_simps)

crunches create_cap, update_cdt
for tcb_ready_time_inv'[wp]: "\<lambda>s::det_state. P (tcb_ready_time t s)"
and sorted_release_q[wp]: "\<lambda>s::det_state. sorted_release_q s"
and valid_release_q[wp]: "\<lambda>s::det_state. valid_release_q s"
  (wp: crunch_wps simp: crunch_simps)

crunches set_untyped_cap_as_full
for valid_release_q[wp]: valid_release_q

lemma cap_insert_valid_release_q[wp]:
  "\<lbrace>valid_release_q\<rbrace>
   cap_insert new_cap src_slot dest_slot \<lbrace>\<lambda>_ . valid_release_q::det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: cap_insert_def update_sched_context_def set_object_def
                  wp: get_object_wp hoare_drop_imp simp_del: fun_upd_apply)


lemma valid_release_imp_sorted: "valid_release_q s \<Longrightarrow> sorted_release_q s"
  by (clarsimp simp: valid_release_q_def)

context DetSchedAux_AI_det_ext begin

lemma invoke_untyped_valid_sched:
  "\<lbrace>invs and valid_untyped_inv ui and ct_active and valid_sched and valid_idle and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     invoke_untyped ui
   \<lbrace> \<lambda>_ . valid_sched :: det_ext state \<Rightarrow> _ \<rbrace>"
  including no_pre
  apply (rule hoare_pre)
   apply (rule_tac I="invs and valid_untyped_inv ui and ct_active and
                      (\<lambda>s. scheduler_action s = resume_cur_thread)"
          in valid_sched_tcb_state_preservation_gen)
            apply (wp invoke_untyped_st_tcb_at)
            apply simp
            apply (wpsimp wp: invoke_untyped_etcb_at invoke_untyped_active_sc_tcb_at
                              invoke_untyped_budget_sufficient invoke_untyped_budget_ready)+
        apply (rule_tac Q="\<lambda> s. P (tcb_ready_time t s) \<and> active_sc_tcb_at t s" in hoare_post_imp_dc[rotated])
         apply clarsimp
        apply (wpsimp wp: invoke_untyped_tcb_ready_time)+
    apply (rule hoare_post_impErr, rule hoare_pre, rule invoke_untyp_invs,
           simp_all add: invs_valid_idle)[1]
   apply (rule_tac f="\<lambda>s. P (scheduler_action s)" in hoare_lift_Pf)
    apply (rule_tac f="\<lambda>s. x (ready_queues s)" in hoare_lift_Pf)
     apply (rule_tac f="\<lambda>s. xa (cur_domain s)" in hoare_lift_Pf)
      apply wp+
  apply auto
  done

end

crunches create_cap,cap_insert
for valid_sched_action[wp]: "valid_sched_action :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps valid_release_q_lift sorted_release_q_lift valid_sched_action_lift
   ignore: create_cap_ext simp: crunch_simps)

crunch valid_sched[wp]: create_cap,cap_insert "valid_sched :: det_ext state \<Rightarrow> bool"
  (wp: valid_sched_lift simp: )

(* misc lemmas *)

lemma valid_sched_switch_thread_is_schedulable:
  "\<lbrakk>valid_sched s; scheduler_action s = switch_thread thread\<rbrakk> \<Longrightarrow>
     is_schedulable_opt thread (in_release_queue thread s) s = Some True"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
       is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def get_tcb_rev
       in_release_queue_def)

lemma simple_sched_act_not[simp]:
  "simple_sched_action s \<Longrightarrow> scheduler_act_not t s"
  by (clarsimp simp: simple_sched_action_def scheduler_act_not_def)

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

lemma is_activatable_trivs[iff]:
  "is_activatable_2 ct (switch_thread t) kh"
  "is_activatable_2 ct choose_new_thread kh"
  by (simp_all add: is_activatable_def)

lemma weak_valid_sched_action_trivs[iff]:
  "weak_valid_sched_action_2 resume_cur_thread kh curtime rq"
  "weak_valid_sched_action_2 choose_new_thread kh curtime rq"
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
  "valid_sched_action_2 choose_new_thread kh ct cdom curtime rq"
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

(* Move? *)
lemma get_tcb_st_tcb_at:
  "get_tcb t s = Some y \<Longrightarrow> st_tcb_at \<top> t s"
  apply (simp add: get_tcb_def pred_tcb_at_def obj_at_def is_tcb
              split: option.splits kernel_object.splits)
  done

lemma etcbs_of_update_unrelated:
  "\<lbrakk> kh ref = Some (TCB tcb); etcb_of tcb = etcb_of tcb' \<rbrakk> \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB tcb') else kh r) = etcbs_of' kh"
  by (auto simp: etcbs_of'_def)

lemma etcbs_of_update_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_state_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

(* FIXME move *)
lemma runnable_eq_active: "runnable = active"
  apply (rule ext)
  apply (case_tac st, simp_all)
  done

(* FIXME move *)
lemma st_tcb_at_not:
  "st_tcb_at (\<lambda>st. \<not> P st) t s = (\<not> st_tcb_at P t s \<and> tcb_at t s)"
  apply (clarsimp simp: not_pred_tcb)
  apply (fastforce simp: st_tcb_at_tcb_at)
  done

lemma etcbs_of_arch_state[simp]:
  "get_tcb ref s = Some tcb \<Longrightarrow>
  etcbs_of' (\<lambda>r. if r = ref then Some (TCB (tcb_arch_update f tcb)) else kheap s r) = etcbs_of' (kheap s)"
  by (auto simp: etcbs_of_update_unrelated dest!: get_tcb_SomeD)

lemma ct_in_q_valid_blocked_ct_upd:
  "\<lbrakk>ct_in_q s; valid_blocked s\<rbrakk> \<Longrightarrow> valid_blocked (s\<lparr>cur_thread := thread\<rparr>)"
  apply (clarsimp simp: valid_blocked_def ct_in_q_def)
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply (case_tac "t=cur_thread s")
   apply (simp add: not_queued_def not_in_release_q_def)
   apply (case_tac st, (force simp: st_tcb_at_def obj_at_def)+)
   done

lemma ct_in_q_arch_state_upd[simp]:
  "ct_in_q (s\<lparr>arch_state := f\<rparr>) = ct_in_q s"
  by (simp add: ct_in_q_def)

lemma ct_in_q_machine_state_upd[simp]:
  "ct_in_q (s\<lparr>machine_state := f\<rparr>) = ct_in_q s"
  by (simp add: ct_in_q_def)

crunch ct_in_q[wp]: do_machine_op ct_in_q

lemma valid_ready_qs_trivial[simp]: "valid_ready_qs_2 (\<lambda>_ _. []) ctime kh"
  by (simp add: valid_ready_qs_def)

lemma sorted_release_trivial[simp]: "sorted_release_q_2 [] kh"
  by (simp add: sorted_release_q_def)

lemma valid_release_trivial[simp]: "valid_release_q_2 [] kh"
  by (simp add: valid_release_q_def)

lemma ct_not_in_q_trivial[simp]: "ct_not_in_q_2 (\<lambda>_ _. []) sa ct"
  by (simp add: ct_not_in_q_def not_queued_def)

lemma st_tcb_at_get_lift:
  "get_tcb thread s = Some y \<Longrightarrow> test (tcb_state y) \<Longrightarrow> st_tcb_at test thread s"
  by (simp add: ct_in_state_def st_tcb_def2)

lemmas det_ext_simps[simp] = select_switch_det_ext_ext_def unwrap_ext_det_ext_ext_def

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

lemma next_thread_queued: "queues p \<noteq> [] \<Longrightarrow> \<exists>p. next_thread queues \<in> set (queues p)"
  apply (clarsimp simp: next_thread_def max_non_empty_queue_def)
  apply (rule_tac x="Max {prio. queues prio \<noteq> []}" in exI)
  apply (rule Max_prop)
   apply simp
  apply blast
  done

lemma etcbs_of'_non_tcb_update:
  "\<lbrakk> kh ref = Some obj'; a_type obj = a_type obj'; a_type obj \<noteq> ATCB \<rbrakk> \<Longrightarrow>
  etcbs_of' (\<lambda>a. if a = ref then Some obj else kh a) = etcbs_of' kh"
  by (rule ext) (auto simp: etcbs_of'_def split: kernel_object.splits)

lemma ct_not_in_q_def2:
  "ct_not_in_q_2 queues sa ct = (sa = resume_cur_thread \<longrightarrow> (\<forall>d p. ct \<notin> set (queues d p)))"
  by (fastforce simp add: ct_not_in_q_def not_queued_def)

(* FIXME move *)
lemma hd_last_length_2: "length ls = 2 \<Longrightarrow> [hd ls, last ls] = ls"
  apply (cases ls; clarsimp)
  by (case_tac list; clarsimp)

lemma ball_mapM_scheme:  (* maybe move? is this generic enough? *)
  assumes x: "\<And>t t'. \<lbrace> \<lambda>s. Q t' s \<and> t' \<noteq> t \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace>"
  and y:  "\<And>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace>"
  shows "distinct xs \<Longrightarrow> \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> mapM (\<lambda>t. f t) xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply (wpsimp wp: hoare_vcg_ball_lift x y)
  done

lemma ball_mapM_x_scheme:
  assumes x: "\<And>t t'. \<lbrace> \<lambda>s. Q t' s \<and> t' \<noteq> t \<rbrace> f t \<lbrace> \<lambda>_. Q t' \<rbrace>"
  and y:  "\<And>t. \<lbrace> Q t and P \<rbrace> f t \<lbrace>\<lambda>_. P \<rbrace>"
  shows "distinct xs \<Longrightarrow> \<lbrace> (\<lambda>s. \<forall>t\<in>set xs. Q t s) and P\<rbrace> mapM_x (\<lambda>t. f t) xs \<lbrace>\<lambda>_. P\<rbrace>"
  by (subst mapM_x_mapM) (wp ball_mapM_scheme x y)

(* FIXME: Move *)
lemma set_object_obj:
  "\<lbrace>obj_at P ptr and K (x \<noteq> ptr)\<rbrace> set_object x ko \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  by (clarsimp simp add: valid_def set_object_def in_monad obj_at_def)

(* FIXME: Move *)
lemma st_tcb_reply_state_refs:
  "\<lbrakk>valid_objs s; sym_refs (state_refs_of s); st_tcb_at ((=) (BlockedOnReply rp)) thread s\<rbrakk>
  \<Longrightarrow> \<exists>reply. (kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some thread)"
  apply (frule (1) st_tcb_at_valid_st2)
  apply (drule (1) sym_refs_st_tcb_atD[rotated])
  apply (clarsimp simp: get_refs_def2 obj_at_def valid_tcb_state_def is_reply
                  split: thread_state.splits if_splits)
  done

(* FIXME move *)
lemma set_filter_all[simp]: "set (filter (\<lambda>x. P x) xs @ filter (\<lambda>x. \<not> P x) xs) = set xs" by auto

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

(* FIXME move *)
lemma length_eq_pair_in_set_zip:
  "length qs = length r \<Longrightarrow> x \<in> set qs \<Longrightarrow> \<exists>b. (x, b) \<in> set (zip qs r)"
  apply (induct qs arbitrary: r; simp)
  apply (safe; case_tac r; fastforce)
  done

lemma in_release_queue_in_release_q:
  "in_release_queue t = in_release_q t"
  by (clarsimp simp: in_release_queue_def in_release_q_def)

(* FIXME maybe move *)
lemma fun_of_m_imp: "f s = ({(b, s')}, False) \<Longrightarrow> (fun_of_m f s = Some b)"
  by (clarsimp simp: fun_of_m_def the_equality)

lemma fun_of_m_iff: "(\<exists>s'. f s = ({(b, s')}, False)) \<longleftrightarrow> (fun_of_m f s = Some b)"
  by (fastforce simp: fun_of_m_def the_equality split: if_split_asm)+

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

(* FIXME: Move *)
definition
  ntfn_sc_ntfn_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "ntfn_sc_ntfn_at P \<equiv> obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> P (ntfn_sc ntfn))"

(* FIXME: move *)
lemma valid_objs_SendEP_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s xa = Some (Endpoint (SendEP x2)))
   \<Longrightarrow> distinct x2"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ep_def)
  done

(* FIXME: move *)
lemma valid_objs_RecvEP_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s xa = Some (Endpoint (RecvEP x2)))
   \<Longrightarrow> distinct x2"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ep_def)
  done

(* FIXME: move *)
lemma valid_objs_WaitingNtfn_distinct:
  "valid_objs s
   \<Longrightarrow> (kheap s xa = Some (Notification notif))
   \<Longrightarrow> ntfn_obj notif = WaitingNtfn x2
   \<Longrightarrow> distinct x2"
  apply (clarsimp simp: valid_objs_def dom_def valid_obj_def)
  apply (fastforce simp: valid_ntfn_def)
  done

lemma valid_sched_not_runnable_not_in_release_q:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (fastforce simp: valid_sched_def valid_release_q_def pred_tcb_at_def
                      not_queued_def not_in_release_q_def obj_at_def)

lemma valid_sched_not_runnable_not_queued:
  "\<lbrakk>valid_sched s; st_tcb_at (\<lambda>ts. \<not> runnable ts) tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s"
  by (fastforce simp: valid_sched_def valid_ready_qs_def  pred_tcb_at_def
                      not_queued_def  obj_at_def)

lemma valid_blocked_except_set_no_active_sc_sum:
  "valid_blocked_except_set {tcbptr} s
   \<Longrightarrow> \<not> active_sc_tcb_at tcbptr s
   \<Longrightarrow> valid_blocked s"
  apply (auto simp: valid_blocked_except_set_def valid_blocked_def)
  done

lemma not_not_in_eq_in: "\<not> not_in_release_q t s \<longleftrightarrow> in_release_queue t s"
  (* this shouldn't be set to iff globally *)
  by (clarsimp simp: in_release_queue_def not_in_release_q_def)

lemma valid_blocked_except_set_in_release_queue_sum:
  "valid_blocked_except_set {tcbptr} s
   \<Longrightarrow> in_release_queue tcbptr s
   \<Longrightarrow> valid_blocked s"
  apply (clarsimp simp: valid_blocked_except_set_def valid_blocked_def)
  apply (case_tac "t = tcbptr")
   apply (fastforce iff: not_not_in_eq_in[symmetric])
  apply (drule_tac x=t in spec; simp)
  done

lemma schedulable_unfold2:
  "((is_schedulable_opt tp b s) = Some X)
   \<Longrightarrow> tcb_at tp s
   \<Longrightarrow> (X = (st_tcb_at runnable tp s \<and> active_sc_tcb_at  tp s \<and> \<not>b))"
  by (clarsimp simp: is_schedulable_opt_def get_tcb_rev is_tcb pred_tcb_at_def obj_at_def
                     active_sc_tcb_at_def
              split: option.splits)


end
