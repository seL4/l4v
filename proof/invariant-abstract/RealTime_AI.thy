(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory RealTime_AI
imports VSpace_AI
begin

lemma maybeM_inv[wp]:
  "\<forall>a. \<lbrace>P\<rbrace> f a \<lbrace>\<lambda>_. P\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> maybeM f opt \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: maybeM_def; fastforce)

crunch inv[wp]: ethread_get, ethread_get_when P

text {* update\_sched\_context *}

lemma update_sched_context_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> update_sched_context ref sc \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: update_sched_context_def get_object_def)

lemma update_sched_context_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> update_sched_context ref sc \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def)
  apply (auto simp: obj_at_def is_tcb_def)
  done

lemma update_sched_context_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> update_sched_context ref sc \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_irq_handlers_def
                      irq_issued_def ran_def)
  apply (subgoal_tac "caps_of_state s (a, b) = Some cap")
   apply fastforce
  apply (subst cte_wp_caps_of_lift; auto simp: cte_wp_at_cases)
  done

lemma update_sched_context_valid_objs[wp]:
  "\<lbrace>\<lambda>s. valid_objs s \<and> valid_sched_context sc s\<rbrace> update_sched_context ref sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma refs_in_get_refs:
  "(x, ref) \<in> get_refs REF ntfn \<Longrightarrow> ref = REF"
  by (auto simp: get_refs_def split: option.splits)

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)


text {* sched\_context\_donate and others *}

lemma sched_context_donate_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def update_sched_context_def get_object_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma sched_context_donate_interrupt_states[wp]: "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def update_sched_context_def get_object_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma sched_context_donate_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemmas sched_context_donate_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF sched_context_donate_caps_of_state
                                  sched_context_donate_interrupt_states]

lemma sched_context_donate_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def update_sched_context_def get_object_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma sched_context_donate_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  by (auto simp: pspace_in_kernel_window_atyp_lift sched_context_donate_typ_at
                 sched_context_donate_arch)

lemma sched_context_donate_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_cap_refs_in_kernel_window[wp]: (* delete valid_objs? *)
      "\<lbrace>valid_objs and cap_refs_in_kernel_window\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

crunch arch [wp]: set_reply "\<lambda>s. P (arch_state s)"
  (simp: get_object_def)

lemma scheduling_context_update [iff]: (* move it elsewhere? *)
  "valid_sched_context sc (trans_state f s) = valid_sched_context sc s"
  apply (simp add: valid_sched_context_def valid_bound_obj_def split: option.splits)
  done

lemma sched_context_donate_valid_objs [wp]: (* replace it with Miki's version *)
  "\<lbrace>valid_objs and sc_at scp and tcb_at tcbp\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def
                  wp: hoare_drop_imp hoare_vcg_conj_lift get_sched_context_wp)
       apply (wpsimp simp: set_tcb_obj_ref_def set_object_def get_sched_context_def get_object_def)+
  apply safe
      apply (clarsimp simp: valid_objs_def dest!: get_tcb_SomeD)
      apply (erule_tac x = scp in ballE)
       apply (auto simp add: valid_bound_obj_def is_ntfn_def obj_at_def valid_obj_def is_tcb_def
                             valid_sched_context_def is_reply_def list_all_def
                      split: if_splits option.splits)+
  done

lemma sched_context_donate_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_ifunsafe[wp]: (* delete valid_objs? *)
  "\<lbrace>valid_objs and if_unsafe_then_cap\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_zombies[wp]: (* delete valid_objs? *)
  "\<lbrace>valid_objs and zombies_final\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

lemma sched_context_donate_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma sched_context_donate_iflive[wp]:
  "\<lbrace>\<lambda>s.  if_live_then_nonz_cap s\<rbrace>
  sched_context_donate scp tcbp
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  sorry

lemma sched_context_donate_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def wp: hoare_drop_imp)

text {* reply\_remove and others *}

lemma reply_remove_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sched_context_def get_object_def
                   update_sk_obj_ref_def set_simple_ko_def set_object_def get_simple_ko_def
                   get_sched_context_def reply_unlink_tcb_def set_thread_state_def case_option_If2
                   get_thread_state_def thread_get_def)

lemma reply_remove_interrupt_states[wp]: "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sched_context_def get_object_def
                   update_sk_obj_ref_def set_simple_ko_def set_object_def get_simple_ko_def
                   get_sched_context_def reply_unlink_tcb_def set_thread_state_def case_option_If2
                   get_thread_state_def thread_get_def)

lemma reply_remove_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> reply_remove r \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemmas reply_remove_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF reply_remove_caps_of_state
                                  reply_remove_interrupt_states]

lemma reply_remove_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (wpsimp simp: reply_unlink_sc_def reply_unlink_tcb_def update_sk_obj_ref_def
                      get_sched_context_def
                  wp: hoare_drop_imp)+
  done

lemma reply_remove_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  sorry


lemma reply_remove_valid_objs [wp]:
  "\<lbrace>valid_objs and reply_at r\<rbrace> reply_remove r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  sorry

lemma reply_remove_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> reply_remove r \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> reply_remove r \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> reply_remove r \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

lemma reply_remove_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> reply_remove r \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  sorry

lemma reply_remove_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> reply_remove r \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  sorry

lemma reply_remove_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_remove r \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma reply_remove_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  reply_remove r
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  sorry

lemma reply_remove_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imp)

(*
lemma reply_remove_[wp]:
      "\<lbrace>\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<rbrace>"
*)

text {* invs *} (* most of these below will probably require a bunch more of lemmas *)

crunches update_sched_context
  for valid_irq_states[wp]: valid_irq_states

lemma state_hyp_refs_of_sc_update: "\<And>s sc val n. typ_at (ASchedContext n) sc s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := kheap s(sc \<mapsto> SchedContext val n)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp: ARM.state_hyp_refs_of_def obj_at_def ARM.hyp_refs_of_def
                 split: kernel_object.splits)
  done

(*
crunch typ_at[wp]: postpone, sched_context_bind_tcb "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (ignore: check_cap_at setNextPC zipWithM
       wp: hoare_drop_imps mapM_x_wp' maybeM_inv select_wp
     simp: crunch_simps)
*)
lemma sc_and_timer_empty_fail:
  "empty_fail sc_and_timer"
  sorry

(* FIXME: move *)
lemma tcb_at_typ_at:
  "\<lbrace>typ_at ATCB t\<rbrace> f \<lbrace>\<lambda>_. typ_at ATCB t\<rbrace> \<Longrightarrow> \<lbrace>tcb_at t\<rbrace> f \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ)

lemma valid_bound_tcb_typ_at:
  "\<forall>p. \<lbrace>\<lambda>s. typ_at ATCB p s\<rbrace> f \<lbrace>\<lambda>_ s. typ_at ATCB p s\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_tcb tcb s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_tcb tcb s\<rbrace>"
  apply (clarsimp simp: valid_bound_obj_def split: option.splits)
  apply (wpsimp wp: hoare_vcg_all_lift tcb_at_typ_at static_imp_wp)
  done

(*
crunch bound_tcb[wp]: schedule_tcb "valid_bound_tcb t"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM)

crunch typ_at[wp]: schedule_tcb "\<lambda>s. P (typ_at T p s)"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM) 

crunch cap_to[wp]: sched_context_donate, sort_queue, schedule_tcb, maybe_donate_sc, maybe_return_sc
 "ex_nonz_cap_to p:: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps maybeM_inv) 
*)
crunch typ_at[wp]: get_sched_context, set_sched_context "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv simp: get_object_def)
crunch typ_at[wp]: sched_context_unbind_yield_from "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps ignore: get_ntfn_obj_ref)

lemma sched_context_unbind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_unbind_tcb scref \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imp
           simp: sched_context_unbind_tcb_def)

crunch typ_at[wp]: unbind_from_sc, sched_context_maybe_unbind_ntfn, reply_unlink_sc, sched_context_clear_replies, sched_context_unbind_yield_from "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps simp: get_tcb_obj_ref_def ignore: get_ntfn_obj_ref)

lemma schedule_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  sorry

lemma sched_context_unbind_all_tcbs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_unbind_all_tcbs scref \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def)

lemma sched_context_update_consumed_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_update_consumed param_a \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace> "
  by (wpsimp simp: sched_context_update_consumed_def get_sched_context_def get_object_def)

lemma postpone_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> postpone param_a \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: postpone_def wp: hoare_drop_imp)

lemma refill_unblock_check_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> refill_unblock_check param_a \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: refill_unblock_check_def set_refills_def get_refills_def is_round_robin_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma schedule_tcb_is_original_cap[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (is_original_cap s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def reschedule_required_def set_scheduler_action_def
                   tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def is_schedulable_def
                   get_sched_context_def get_object_def)

lemma get_sched_context_inv[wp]: "\<lbrace>P\<rbrace> get_sched_context sc_ptr \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: get_sched_context_def wp: get_object_wp)


lemma postpone_inv[wp]:
  "(\<And>s f. P (trans_state f s) = P s) \<Longrightarrow> \<lbrace>(\<lambda>s. P (s\<lparr>reprogram_timer := True\<rparr>))\<rbrace> postpone sc_ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: postpone_def wp: dxo_wp_weak hoare_drop_imp
         | (drule_tac x="s\<lparr>reprogram_timer := True\<rparr>" in meta_spec, simp))+


lemma end_timeslice_inv[wp]:
  "(\<And>s f. P (trans_state f s) = P s) \<Longrightarrow> \<lbrace>P\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>rv. P\<rbrace>"
  sorry

(* can we say this? what about charge_budget?
lemma check_budget_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
   \<Longrightarrow> \<lbrace>P\<rbrace> check_budget \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: check_budget_def)
  sorry
*)

lemma get_refills_inv[wp]: "\<lbrace>P\<rbrace> get_refills sc_ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: get_refills_def get_sched_context_def wp: get_object_wp)

lemma sort_queue_notin_inv: "\<lbrace>K (t \<notin> set ls) and P t\<rbrace> sort_queue ls \<lbrace>\<lambda>rv. P t\<rbrace>"
  apply (wpsimp simp: sort_queue_def wp: mapM_wp)
  apply auto
  done


lemma reply_push_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t and K (t \<noteq> caller) and K (t \<noteq> callee)\<rbrace>
  reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  sorry


lemma sched_context_donate_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t and K (t \<noteq> tcb_ptr)\<rbrace> (* need more precondition? *)
  sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def update_sched_context_def get_sched_context_def
                wp: set_object_wp get_object_wp)
  sorry

lemma sched_context_update_consumed_if_live:
  "\<lbrace>if_live_then_nonz_cap and valid_objs\<rbrace> (* delete obj_at live param_a? *)
  sched_context_update_consumed param_a \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def if_live_then_nonz_cap_def wp: hoare_drop_imp)
  sorry

end