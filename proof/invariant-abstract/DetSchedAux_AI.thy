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
  for rqueues[wp]: "\<lambda>s. P (ready_queues s)"
  and schedact[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and release_queue[wp]: "\<lambda>s. P (release_queue s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps dxo_wp_weak)

lemma set_cap_etcbs[wp]:
  "set_cap p c \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto simp: obj_at_def etcbs_of'_def etcb_of_def elim!: rsubst[where P=P])
  done

crunch etcbs[wp]: create_cap, cap_insert "\<lambda>s. P (etcbs_of s)"
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
  assumes invoke_untyped_active_sc_tcb_at:  (* are the preconditions correct? *)
    "\<And>i t. \<lbrace>\<lambda>s :: det_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and active_sc_tcb_at t and ct_active and valid_untyped_inv i
       and (\<lambda>s. scheduler_action s = resume_cur_thread)) s\<rbrace> invoke_untyped i
       \<lbrace>\<lambda>_ s. active_sc_tcb_at t s\<rbrace>"
  assumes invoke_untyped_budget_sufficient: (* check precondition *)
    "\<And>t i. \<lbrace>\<lambda>s::det_ext state. (invs and st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t
       and (\<lambda>s. (budget_sufficient t s)) and ct_active and valid_untyped_inv i
       and (\<lambda>s. scheduler_action s = resume_cur_thread)) s\<rbrace>
                 invoke_untyped i \<lbrace>\<lambda>_ s. (budget_sufficient t s)\<rbrace>"
  assumes invoke_untyped_budget_ready: (* check precondition *)
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
(*  assumes invoke_untyped_budget_sufficient[wp]:
    "\<And>P t i. \<lbrace>\<lambda>s::det_ext state. P (budget_sufficient t s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (budget_sufficient t s)\<rbrace>"
  assumes invoke_untyped_budget_ready[wp]:
    "\<And>P t i. \<lbrace>\<lambda>s::det_ext state. P (budget_ready t s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (budget_ready t s)\<rbrace>"
*)  assumes init_arch_objects_valid_blocked[wp]:
    "\<And>t r n sz refs. \<lbrace>valid_blocked::det_ext state \<Rightarrow> _\<rbrace> init_arch_objects t r n sz refs \<lbrace>\<lambda>_. valid_blocked\<rbrace>"
  assumes invoke_untyped_idle_thread[wp]:
    "\<And>P i. \<lbrace>\<lambda>s::det_ext state. P (idle_thread s)\<rbrace> invoke_untyped i \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"

lemmas mapM_x_defsym = mapM_x_def[symmetric]

crunches update_cdt_list,set_cdt
for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at t ts s)"
and typ_at[wp]: "\<lambda>s. P (typ_at T t s)"
and active_sc_tcb_at'[wp]: "\<lambda>s. P (active_sc_tcb_at t s)"

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
            apply simp+
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
         apply ((erule pred_tcb_weakenE, simp, case_tac "itcb_state tcb", simp+)+)[7]
  apply (rule conjI)
   apply (clarsimp simp add: valid_release_q_def)
   apply (drule_tac x=t in bspec)
    apply simp
   apply clarsimp
   apply (subgoal_tac "st_tcb_at runnable t b \<and> active_sc_tcb_at t b")
    apply simp
   apply (rule_tac conjI[OF use_valid[OF _ st_tcb] use_valid[OF _ bound_sc]], assumption)
     apply simp
     apply ((erule pred_tcb_weakenE, simp, case_tac "itcb_state tcb", simp+)+)[3]
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
    apply (rule hoare_post_impErr, rule hoare_pre, rule invoke_untyp_invs,
           simp_all add: invs_valid_idle)[1]
   apply (rule_tac f="\<lambda>s. P (scheduler_action s)" in hoare_lift_Pf)
    apply (rule_tac f="\<lambda>s. x (ready_queues s)" in hoare_lift_Pf)
     apply (rule_tac f="\<lambda>s. xa (cur_domain s)" in hoare_lift_Pf)
      apply wp+
  apply auto
  done

end

crunch valid_sched_action[wp]: create_cap,cap_insert "valid_sched_action :: det_ext state \<Rightarrow> bool"
  (wp: valid_sched_action_lift ignore: create_cap_ext)

crunch valid_sched[wp]: create_cap,cap_insert "valid_sched :: det_ext state \<Rightarrow> bool"
  (wp: valid_sched_lift crunch_wps)

crunch inv[wp]: get_tcb_queue "\<lambda>s. P s"

end
