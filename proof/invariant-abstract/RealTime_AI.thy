(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory RealTime_AI
imports VSpace_AI
begin

lemmas MIN_BUDGET_nonzero = MIN_BUDGET_pos[simplified word_neq_0_conv[symmetric]]

lemmas refill_sufficient_defs = refill_sufficient_def refill_capacity_def

(* FIXME - Move Invariants_AI *)
lemma invs_exst [iff]:
  "invs (trans_state f s) = invs s"
  by (simp add: invs_def valid_state_def)

text \<open>update\_sched\_context\<close>

lemma update_sched_context_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: update_sched_context_def get_object_def)

lemma update_sched_context_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s \<and> ref \<noteq> idle_sc_ptr\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma update_sched_context_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_irq_handlers_def
                      irq_issued_def ran_def)
  apply (subgoal_tac "caps_of_state s (a, b) = Some cap")
   apply fastforce
  apply (subst cte_wp_caps_of_lift; auto simp: cte_wp_at_cases)
  done

lemma update_sched_context_valid_objs[wp]:
  "\<lbrace>\<lambda>s. valid_objs s \<and> valid_sched_context sc s\<rbrace> update_sched_context ref (\<lambda>_. sc) \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma update_sched_context_fault_tcbs_valid_states[wp]:
  "update_sched_context ref f \<lbrace>fault_tcbs_valid_states\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def)
  done

lemma update_sched_context_valid_objs_same:
  "\<lbrace>\<lambda>s. valid_objs s \<and> (\<forall>sc. valid_sched_context sc s \<longrightarrow> valid_sched_context (f sc) s)\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemmas sc_refills_update_valid_objs[wp]
  = update_sched_context_valid_objs_same[where f="sc_refills_update f" for f,
                                         simplified valid_sched_context_def, simplified]

lemmas sc_consumed_update_valid_objs[wp]
  = update_sched_context_valid_objs_same[where f="sc_consumed_update f" for f,
                                         simplified valid_sched_context_def, simplified]

lemmas sc_refill_max_update_valid_objs[wp]
  = update_sched_context_valid_objs_same[where f="sc_refill_max_update f" for f,
                                         simplified valid_sched_context_def, simplified]

lemma update_sched_context_valid_objs_update:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
        (\<forall>sc n. ko_at (SchedContext sc n) ref s \<longrightarrow>
                  valid_sched_context sc s \<longrightarrow> valid_sched_context (f sc) s)\<rbrace>
   update_sched_context ref f
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma refs_in_get_refs:
  "(x, ref) \<in> get_refs REF ntfn \<Longrightarrow> ref = REF"
  by (auto simp: get_refs_def split: option.splits)

text \<open>update_sched_context/get_sc_obj_ref\<close>

lemma get_sc_obj_ref_inv[simp, wp]:
  "\<lbrace>P\<rbrace> get_sc_obj_ref f t \<lbrace>\<lambda>r. P\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def get_sched_context_def get_object_def)

crunches update_sched_context
  for no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"

lemma set_sc_ntfn_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_ntfn ntfn\<rbrace>
   set_sc_obj_ref sc_ntfn_update t ntfn
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: update_sched_context_def obj_at_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma set_sc_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_tcb ntfn\<rbrace>
   set_sc_obj_ref sc_tcb_update t ntfn
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma set_sc_yf_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_tcb ntfn\<rbrace>
   set_sc_obj_ref sc_yield_from_update t ntfn
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma update_sched_context_sc_replies_update_valid_objs[wp]:
  "\<lbrace>valid_objs and
    (\<lambda>s. \<forall>x. list_all (\<lambda>rp. reply_at rp s) x \<longrightarrow> list_all (\<lambda>rp. reply_at rp s) (f x)) and
    K (\<forall>x. distinct x \<longrightarrow> distinct (f x))\<rbrace>
   update_sched_context t (sc_replies_update f)
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def a_type_def)
  done

lemma set_sc_replies_valid_objs[wp]:
  "\<lbrace>valid_objs and (\<lambda>s. list_all (\<lambda>rp. reply_at rp s) replies) and K (distinct replies)\<rbrace>
   set_sc_obj_ref sc_replies_update t replies
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by wpsimp

lemma set_sc_ntfn_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case ntfn of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCNtfn)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCNtfn})))\<rbrace>
   set_sc_obj_ref sc_ntfn_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def
                 wp: get_object_wp)
  by (fastforce elim!: rsubst[where P=P]
                 simp: state_refs_of_def obj_at_def Un_def split_def Collect_eq get_refs_def2
                split: option.splits if_splits)

lemma set_sc_tcb_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case tcb of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCTcb)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCTcb})))\<rbrace>
   set_sc_obj_ref sc_tcb_update t tcb
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def wp: get_object_wp)
  by (fastforce elim!: rsubst[where P=P]
                 simp: state_refs_of_def obj_at_def Un_def split_def  Collect_eq get_refs_def2
                split: option.splits if_splits)

lemma set_sc_yf_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case tcb of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCYieldFrom)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCYieldFrom})))\<rbrace>
   set_sc_obj_ref sc_yield_from_update t tcb
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def
                wp: get_object_wp)
  by (fastforce elim!: rsubst[where P=P]
                 simp: state_refs_of_def obj_at_def Un_def split_def  Collect_eq get_refs_def2
                split: option.splits if_splits)

lemma set_sc_replies_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(sc := {p. if snd p = SCReply
                                         then hd_opt replies = Some (fst p)
                                         else p \<in> state_refs_of s sc}))\<rbrace>
    set_sc_obj_ref sc_replies_update sc replies
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def
                  wp: get_object_wp
            simp_del: fun_upd_apply)
  by (fastforce simp: obj_at_def state_refs_of_def get_refs_def2
               split: option.splits if_splits
               elim!: rsubst[of P])

lemma update_sched_context_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s) \<and> sc_replies_sc_at (\<lambda>x. hd_opt (f x) = hd_opt x) sc s\<rbrace>
    update_sched_context sc (sc_replies_update f)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def
                  wp: get_object_wp
            simp_del: fun_upd_apply)
  apply (clarsimp simp: obj_at_def state_refs_of_def get_refs_def2 sc_at_pred_n_def
               split: option.splits if_splits
               elim!: rsubst[of P])
  by (rule ext; simp)

text \<open>set_reply_obj_ref\<close>

crunches update_sk_obj_ref
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and only_idle[wp]: "only_idle"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and valid_arch[wp]: "valid_arch_state"
 and valid_irq_states[wp]: "valid_irq_states"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and valid_asid_map[wp]: "valid_asid_map"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and valid_ioc[wp]: "valid_ioc"
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_mdb[wp]: valid_mdb
 and valid_idle[wp]: valid_idle
 and fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set TS"
 and zombies[wp]: zombies_final
 and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (simp: crunch_simps wp: crunch_wps)

lemma set_reply_sc_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_sc sc\<rbrace> set_reply_obj_ref reply_sc_update rptr sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_simple_ko_valid_objs get_simple_ko_wp
          simp: update_sk_obj_ref_def obj_at_def split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_reply_def)
  done

lemma set_reply_sc_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound new_sc \<longrightarrow> ex_nonz_cap_to rptr s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_reply_obj_ref reply_sc_update rptr new_sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=rptr in spec)
  apply (clarsimp simp: obj_at_def live_def live_reply_def)
  done

lemma set_reply_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_tcb tcb\<rbrace> set_reply_obj_ref reply_tcb_update rptr tcb \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_simple_ko_valid_objs get_simple_ko_wp
          simp: update_sk_obj_ref_def obj_at_def split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE[where x=rptr])
  apply (auto simp: valid_obj_def valid_reply_def obj_at_def)
  done

lemma set_reply_tcb_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound new_tcb \<longrightarrow> ex_nonz_cap_to rptr s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_reply_obj_ref reply_tcb_update rptr new_tcb
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=rptr in spec)
  apply (clarsimp simp: obj_at_def live_def live_reply_def)
  done

lemma set_reply_sc_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(r := {p. if snd p = ReplySchedContext
                                        then sc = Some (fst p)
                                        else p \<in> state_refs_of s r }))\<rbrace>
    set_reply_obj_ref reply_sc_update r sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_object_def
                  wp: get_sched_context_wp get_simple_ko_wp)
  by (fastforce elim!: rsubst[of P] simp: state_refs_of_def obj_at_def get_refs_def2)

lemma set_reply_tcb_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, ReplyTCB)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = ReplyTCB})))\<rbrace>
   set_reply_obj_ref reply_tcb_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_object_def
                  wp: get_sched_context_wp get_simple_ko_wp)
  apply (fastforce elim!: rsubst[where P=P]
                    simp: state_refs_of_def obj_at_def Un_def split_def Collect_eq get_refs_def2
                   split: option.splits if_splits)
  done

lemma gscn_sc_ntfn_sc_at:
  "\<lbrace>\<top>\<rbrace> get_sc_obj_ref sc_ntfn scp \<lbrace>\<lambda>rv. sc_ntfn_sc_at (\<lambda>ntfn. rv = ntfn) scp\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_ntfn_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gsct_sc_ntfn_sc_at:
  "\<lbrace>\<top>\<rbrace> get_sc_obj_ref sc_tcb scp \<lbrace>\<lambda>rv. sc_tcb_sc_at (\<lambda>tcb. rv = tcb) scp\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_tcb_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gscyf_sc_ntfn_sc_at:
  "\<lbrace>\<top>\<rbrace> get_sc_obj_ref sc_yield_from scp \<lbrace>\<lambda>rv. sc_yf_sc_at (\<lambda>yf. rv = yf) scp\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_yf_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gscrpls_sc_replies_at:
  "\<lbrace>\<top>\<rbrace> liftM sc_replies $ get_sched_context scp \<lbrace>\<lambda>rv. sc_replies_sc_at (\<lambda>rs. rv = rs) scp\<rbrace>"
  by (wpsimp simp: sc_replies_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gscn_sp:
  "\<lbrace>P\<rbrace> get_sc_obj_ref sc_ntfn scp \<lbrace>\<lambda>rv. sc_ntfn_sc_at (\<lambda>ntfn. rv = ntfn) scp and P\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_ntfn_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gsct_sp:
  "\<lbrace>P\<rbrace> get_sc_obj_ref sc_tcb scp \<lbrace>\<lambda>rv. sc_tcb_sc_at (\<lambda>tcb. rv = tcb) scp and P\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_tcb_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gscyf_sp:
  "\<lbrace>P\<rbrace> get_sc_obj_ref sc_yield_from scp \<lbrace>\<lambda>rv. sc_yf_sc_at (\<lambda>yf. rv = yf) scp and P\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def sc_yf_sc_at_def obj_at_def wp: get_sched_context_wp)

lemma gscrpls_sp:
  "\<lbrace>P\<rbrace> liftM sc_replies $ get_sched_context scp \<lbrace>\<lambda>rv. sc_replies_sc_at (\<lambda>rs. rv = rs) scp and P\<rbrace>"
  by (wpsimp simp: sc_replies_sc_at_def obj_at_def wp: get_sched_context_wp)


text \<open>set_tcb_obj_ref/get_tcb_obj_ref\<close>

crunches set_tcb_obj_ref,get_tcb_obj_ref
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_irq_states[wp]: "valid_irq_states"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (simp: Let_def wp: hoare_drop_imps)

crunches get_tcb_obj_ref
 for valid_objs[wp]: valid_objs
 and iflive[wp]: "if_live_then_nonz_cap"
 and valid_mdb[wp]: valid_mdb
 and zombies[wp]: zombies_final
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_ioc[wp]: "valid_ioc"
 and valid_idle[wp]: valid_idle
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and valid_arch[wp]: "valid_arch_state"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and only_idle[wp]: "only_idle"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and valid_asid_map[wp]: "valid_asid_map"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

lemma ex_nonz_cap_to_sched_act_update[simp]:
  "ex_nonz_cap_to p (scheduler_action_update f s) = ex_nonz_cap_to p s"
  by (simp add: ex_nonz_cap_to_def)

lemma valid_mdb_sched_act_update[simp]:
  "valid_mdb (scheduler_action_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

lemma valid_machine_state_sched_act_update[simp]:
  "valid_machine_state (scheduler_action_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

crunches set_thread_state_act
 for aligned[wp]: pspace_aligned
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "tcb_at tptr"
 and st_tcb_at[wp]: "\<lambda>s. Q( st_tcb_at P tptr s)"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_irq_states[wp]: "valid_irq_states"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_objs[wp]: valid_objs
 and iflive[wp]: "if_live_then_nonz_cap"
 and nonz_cap_to[wp]: "ex_nonz_cap_to p"
 and valid_mdb[wp]: valid_mdb
 and zombies[wp]: zombies_final
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_ioc[wp]: "valid_ioc"
 and valid_idle[wp]: valid_idle
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and valid_arch[wp]: "valid_arch_state"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and only_idle[wp]: "only_idle"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and valid_asid_map[wp]: "valid_asid_map"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and arch_state[wp]: "\<lambda>s. P (arch_state s)"
 and aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and valid_objs[wp]: valid_objs
 and sc_at[wp]: "sc_at sc_ptr"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"


text \<open>possible_switch_to invariants\<close>

lemma valid_irq_states_ready_queues_update[simp]:
  "valid_irq_states (ready_queues_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)

lemma valid_irq_states_release_queue_update[simp]:
  "valid_irq_states (release_queue_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)

lemma valid_irq_states_reprogram_timer_update[simp]:
  "valid_irq_states (reprogram_timer_update f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)

(* FIXME RT: move to Invariants_AI *)
lemma cur_tcb_ready_queues_update[simp]:
  "cur_tcb (ready_queues_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma cur_sc_tcb_ready_queues_update[simp]:
  "cur_sc_tcb (ready_queues_update f s) = cur_sc_tcb s"
  by (simp add: cur_sc_tcb_def)

(* FIXME: move to Invariants_AI *)
lemma cur_tcb_release_queue_update[simp]:
  "cur_tcb (release_queue_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME RT: move to Invariants_AI *)
lemma cur_tcb_reprogram_timer_update[simp]:
  "cur_tcb (reprogram_timer_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

(* FIXME: move to Invariants_AI *)
lemma valid_ioc_ready_queues_update[simp]:
  "valid_ioc (ready_queues_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

(* FIXME: move to Invariants_AI *)
lemma valid_ioc_release_queue_update[simp]:
  "valid_ioc (release_queue_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

(* FIXME: move to Invariants_AI *)
lemma valid_mdb_ready_queues_update[simp]:
  "valid_mdb (ready_queues_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

(* FIXME: move to Invariants_AI *)
lemma valid_mdb_release_queue_update[simp]:
  "valid_mdb (release_queue_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

(* FIXME: move to Invariants_AI *)
lemma (in pspace_update_eq) ex_nonz_cap_to_update[iff]:
  "ex_nonz_cap_to p (f s) = ex_nonz_cap_to p s"
  by (simp add: ex_nonz_cap_to_def)

(* FIXME: do this in Invariants_AI *)
declare release_queue_update.state_refs_update[simp]
declare ready_queues_update.state_refs_update[simp]

(* FIXME: move to Invariants_AI *)
lemma valid_machine_state_ready_queues_update[simp]:
  "valid_machine_state (ready_queues_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME: move to Invariants_AI *)
lemma valid_machine_state_release_queue_update[simp]:
  "valid_machine_state (release_queue_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME RT: move to Invariants_AI *)
lemma valid_machine_state_reprogram_timer_update[simp]:
  "valid_machine_state (reprogram_timer_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

crunches tcb_sched_action,reschedule_required,possible_switch_to,tcb_release_enqueue,tcb_release_remove
 for aligned[wp]: pspace_aligned
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "\<lambda>s. P (tcb_at tptr s)"
 and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P tptr s)"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_irq_states[wp]: "valid_irq_states"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_objs[wp]: valid_objs
 and iflive[wp]: "if_live_then_nonz_cap"
 and nonz_cap_to[wp]: "ex_nonz_cap_to p"
 and valid_mdb[wp]: valid_mdb
 and zombies[wp]: zombies_final
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_ioc[wp]: "valid_ioc"
 and valid_idle[wp]: valid_idle
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and valid_arch[wp]: "valid_arch_state"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and only_idle[wp]: "only_idle"
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and valid_asid_map[wp]: "valid_asid_map"
 and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and arch_state[wp]: "\<lambda>s. P (arch_state s)"
 and aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and valid_objs[wp]: valid_objs
 and sc_at[wp]: "sc_at sc_ptr"
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  (simp: Let_def reprogram_timer_update_arch.state_refs_update Let_def
   wp: hoare_drop_imps hoare_vcg_if_lift2 mapM_wp
   ignore: set_tcb_obj_ref get_tcb_obj_ref)



text \<open>sched\_context\_donate and others\<close>

lemma sched_context_donate_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
       wp: hoare_drop_imp)

lemma sched_context_donate_irq_node[wp]:
 "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
   sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def get_object_def get_sc_obj_ref_def
                   get_sched_context_def test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_interrupt_states[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
    sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def get_object_def get_sc_obj_ref_def
                   get_sched_context_def test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemmas sched_context_donate_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF sched_context_donate_caps_of_state
                                  sched_context_donate_interrupt_states]

lemma sched_context_donate_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_object_def test_reschedule_def
                   get_sched_context_def get_sc_obj_ref_def
               wp: hoare_drop_imp)

lemma sched_context_donate_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  by (auto simp: pspace_in_kernel_window_atyp_lift sched_context_donate_typ_at
                 sched_context_donate_arch)

lemma sched_context_donate_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemma scheduling_context_update [iff]: (* FIXME: move it to Invariants_AI *)
  "valid_sched_context sc (trans_state f s) = valid_sched_context sc s"
  by (simp add: valid_sched_context_def valid_bound_obj_def split: option.splits)

lemma sched_context_donate_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: sched_context_donate_def)
  apply (rule hoare_strengthen_pre_via_assert_backward[of "tcb_at tcbp"])
   apply (rule subst[where s="do _ \<leftarrow> do x \<leftarrow> a; _ \<leftarrow> b x; c od; d od"
                       and t="do x \<leftarrow> a; _ \<leftarrow> b x; _ \<leftarrow> c; d od"
                       and P="\<lambda>h. \<lbrace>_\<rbrace> h \<lbrace>_\<rbrace>" for a b c d]
          , simp add: bind_assoc)
   apply (rule hoare_seq_ext[where B="\<lambda>rv s. Not (tcb_at tcbp s)"]
          , wpsimp wp: set_tcb_obj_ref_wp simp: obj_at_def is_tcb)
   apply (wpsimp wp: weak_if_wp get_sc_obj_ref_wp simp: test_reschedule_def)
  apply (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def test_reschedule_def
                  wp: get_sched_context_wp hoare_drop_imps)
  apply (intro conjI; clarsimp)
   apply (erule (1) obj_at_valid_objsE, fastforce simp: obj_at_def is_sc_obj_def valid_obj_def)+
  done

lemma sched_context_donate_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

lemma sched_context_donate_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
    wp: hoare_drop_imp)

lemma sched_context_donate_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
  wp: hoare_drop_imp)

lemma sched_context_donate_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
    wp: hoare_drop_imp)

lemma sched_context_donate_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
     wp: hoare_drop_imp)

lemma sched_context_donate_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
      wp: hoare_drop_imp)

lemma sched_context_donate_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
    wp: hoare_drop_imp)

lemma sched_context_donate_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

crunches test_reschedule
  for ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  and if_live_then_nonz_cap[wp]: if_live_then_nonz_cap

lemma set_sc_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma sched_context_donate_iflive[wp]:
  "\<lbrace>\<lambda>s.  if_live_then_nonz_cap s \<and>
         ex_nonz_cap_to scp s \<and>
         ex_nonz_cap_to tcbp s \<and>
         valid_objs s\<rbrace>
   sched_context_donate scp tcbp
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def)

lemma sched_context_donate_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
                   test_reschedule_def
               wp: hoare_drop_imp)

text \<open>reply\_remove and others\<close>

lemma reply_remove_irq_node[wp]:
 "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
   reply_remove t r \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_unlink_sc_def get_object_def
                   update_sk_obj_ref_def set_simple_ko_def set_object_def get_simple_ko_def
                   get_sched_context_def reply_unlink_tcb_def set_thread_state_def case_option_If2
                   get_thread_state_def thread_get_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 split_del: if_split)

lemma reply_remove_interrupt_states[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  reply_remove t r \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def get_object_def
                   update_sk_obj_ref_def set_simple_ko_def set_object_def get_simple_ko_def
                   get_sched_context_def reply_unlink_tcb_def set_thread_state_def case_option_If2
                   get_thread_state_def thread_get_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 split_del: if_split)

lemma reply_remove_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> reply_remove t r \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemmas reply_remove_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF reply_remove_caps_of_state
                                  reply_remove_interrupt_states]

lemma reply_remove_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (wpsimp simp: reply_unlink_sc_def reply_unlink_tcb_def update_sk_obj_ref_def
                      get_sched_context_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)
  done

lemma reply_remove_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> reply_remove t r
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def update_sk_obj_ref_def
                   get_sched_context_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_unlink_sc_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: reply_unlink_sc_def liftM_def)
  apply (wpsimp simp: reply_at_typ sc_at_typ
                  wp: valid_sc_typ_list_all_reply[simplified reply_at_typ]
                      hoare_vcg_imp_lift hoare_vcg_ex_lift abs_typ_at_lifts
                      hoare_vcg_all_lift get_simple_ko_wp)
  apply (safe;
         clarsimp elim!: obj_at_valid_objsE
                  simp: valid_obj_def valid_reply_def typ_at_eq_kheap_obj
                        valid_sched_context_def reply_at_typ
                        list_all_iff
                  dest!: set_takeWhileD)
  apply (fastforce intro: list.set_sel | fastforce dest: distinct_tl)+
  done

lemma reply_unlink_sc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  by (wpsimp simp: tcb_at_typ wp: get_simple_ko_wp)

lemma reply_unlink_tcb_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace>
      reply_unlink_tcb t rp
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def get_simple_ko_def get_object_def
                      get_thread_state_def thread_get_def)
  by (auto simp: valid_obj_def valid_reply_def obj_at_def)

lemma reply_unlink_tcb_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (tcb_at t' s)\<rbrace> reply_unlink_tcb t rp \<lbrace>\<lambda>_ s. P (tcb_at t' s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def wp: update_sk_obj_ref_wp gts_wp get_simple_ko_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  done

lemma reply_remove_valid_objs [wp]:
  "reply_remove t r \<lbrace>valid_objs\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: weak_if_wp get_simple_ko_wp)

lemma reply_remove_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> reply_remove t r \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_tcb_at[wp]:
  "\<lbrace>tcb_at t'\<rbrace> reply_remove t r \<lbrace>\<lambda>r. tcb_at t'\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> reply_remove t r \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> reply_remove t r \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> reply_remove t r \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> reply_remove t r \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)


lemma reply_remove_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> reply_remove t r \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)

lemma reply_remove_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_remove t r \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma valid_replies_in_replies_sc_reply_tcb:
  "valid_replies s \<Longrightarrow> sym_refs (state_refs_of s)
   \<Longrightarrow> ko_at (Reply reply) r s
   \<Longrightarrow> sc_replies_sc_at (\<lambda>rs. r \<in> set rs) sc_ptr s
   \<Longrightarrow> reply_tcb reply \<noteq> None"
  apply (clarsimp simp: valid_replies_defs)
  apply (drule subsetD, force)
  apply (clarsimp dest!: sym_refs_st_tcb_atD simp: obj_at_def get_refs_def
                  split: option.splits)
  done

lemma reply_tcb_live:
  "reply_tcb reply \<noteq> None \<Longrightarrow> live (Reply reply)"
  by (simp add: live_def live_reply_def)

lemmas valid_replies_in_replies_sc_live =
  valid_replies_in_replies_sc_reply_tcb[THEN reply_tcb_live]

lemma reply_unlink_sc_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> valid_replies s \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
     reply_unlink_sc sc_ptr reply_ptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: reply_unlink_sc_def)
  apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_disj_lift
                    hoare_vcg_all_lift get_simple_ko_wp)
  apply (safe; (drule(1) ko_at_obj_congD; clarsimp)+)
  apply (subgoal_tac "xa \<in> set (sc_replies scb)")
   apply (fastforce simp: obj_at_def
                   dest!: if_live_then_nonz_capD2 valid_sched_object_reply_at
                          valid_replies_in_replies_sc_live
                   intro: sc_replies_sc_at_ko_atI)
  apply (fastforce intro: list.set_sel)
  done

lemma reply_unlink_tcb_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> reply_unlink_tcb t reply_ptr \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                   get_object_def)

crunch ex_nonz_cap_to[wp]: reply_unlink_tcb, reply_unlink_sc "ex_nonz_cap_to t"
  (wp: hoare_drop_imps)

lemma reply_remove_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to rp
    and (\<lambda>s. reply_tcb_reply_at (\<lambda>p. \<forall>tp. p = (Some tp) \<longrightarrow> ex_nonz_cap_to tp s) rp s)
    and valid_objs and valid_replies and sym_refs o state_refs_of\<rbrace>
   reply_remove t rp
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply = None")
   apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)
  apply (wpsimp simp: obj_at_def reply_tcb_reply_at_def
                  wp: hoare_drop_imp hoare_vcg_if_lift2)
  apply (fastforce simp: live_def live_sc_def
                  dest!: sc_with_reply_SomeD
                   elim: if_live_then_nonz_capD2)
  done

lemma reply_remove_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> reply_remove t r \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  apply (clarsimp simp: reply_remove_def)
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def update_sk_obj_ref_def get_sched_context_def
                   reply_unlink_tcb_def
               wp: hoare_drop_imps hoare_vcg_if_lift2 hoare_vcg_all_lift split_del: if_split)


text \<open>invs\<close> (* most of these below will probably require a bunch more of lemmas *)

(* FIXME RT: move to NonDetMonadVCG *)
lemma empty_fail_put[intro!, simp]:
  "empty_fail (put x)"
  by (simp add: empty_fail_def put_def)

lemma set_refills_empty_fail [simp]: (* FIXME RT: move *)
  "empty_fail (set_refills sc_ptr refills)"
  by (auto simp: set_refills_def get_sched_context_def update_sched_context_def get_object_def
                 set_object_def gets_the_def
          intro!: empty_fail_bind empty_fail_get
          split: kernel_object.splits)

lemma do_extended_op_empty_fail [simp]: (* FIXME RT: move *)
  "empty_fail (do_extended_op eop)"
  by (fastforce simp: do_extended_op_def empty_fail_get mk_ef_def
               intro: empty_fail_bind empty_fail_select_f)

lemma get_sc_active_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) scp s \<longrightarrow> Q (sc_active sc) s\<rbrace>
   get_sc_active scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: get_sc_active_def)

lemma get_sc_refill_capacity_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (sc_refill_capacity usage sc) s\<rbrace>
   get_sc_refill_capacity scp usage
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: get_sc_refill_capacity_def)

lemma get_sc_refill_sufficient_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (sc_refill_sufficient usage sc) s\<rbrace>
   get_sc_refill_sufficient scp usage
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: get_sc_refill_sufficient_def)

lemma read_sched_context_SomeD:
  "read_sched_context scp s = Some sc \<Longrightarrow> \<exists>n. kheap s scp = Some (SchedContext sc n)"
  by (clarsimp simp: read_sched_context_def split: kernel_object.split_asm)

lemma read_sched_context_NoneD:
  "read_sched_context scp s = None \<Longrightarrow> \<not>(\<exists>n sc. kheap s scp = Some (SchedContext sc n))"
  by (clarsimp simp: read_sched_context_def obind_def split: kernel_object.split_asm)

lemma read_sc_refill_ready_SomeD:
  "read_sc_refill_ready scp s = Some b
   \<Longrightarrow> \<exists>sc. read_sched_context scp s = Some sc \<and> sc_refill_ready (cur_time s) sc = b"
  by (clarsimp simp: read_sc_refill_ready_def asks_def)

lemma read_sc_refill_ready_NoneD:
  "read_sc_refill_ready scp s = None \<Longrightarrow> read_sched_context scp s = None"
  by (clarsimp simp: read_sc_refill_ready_def obind_def asks_def split: option.split_asm)

lemma get_sc_refill_ready_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (sc_refill_ready (cur_time s) sc) s\<rbrace>
   get_sc_refill_ready scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: get_sc_refill_ready_def obj_at_def)
    (clarsimp dest!: read_sc_refill_ready_SomeD read_sched_context_SomeD)

lemma get_sc_released_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (sc_released (cur_time s) sc) s\<rbrace>
   get_sc_released scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: get_sc_released_def)

lemma refill_full_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall> sc n. ko_at (SchedContext sc n) scp s \<longrightarrow>
         Q (length (sc_refills sc) = sc_refill_max sc) s\<rbrace>
   refill_full scp
   \<lbrace>Q\<rbrace>"
 by (wpsimp simp: refill_full_def)

crunches
  get_sc_active, get_sc_refill_capacity, get_sc_refill_sufficient, get_sc_refill_ready,
  get_sc_released, get_refills, refill_full
  for inv[wp]: P
  (wp_del: get_sc_active_wp get_sc_refill_ready_wp get_sc_refill_sufficient_wp
           get_sc_released_wp refill_full_wp)

crunches
  sched_context_unbind_yield_from, sched_context_unbind_all_tcbs, postpone,
  unbind_from_sc, sched_context_maybe_unbind_ntfn, reply_unlink_sc,
  sched_context_unbind_reply, schedule_tcb, refill_unblock_check
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_drop_imp hoare_vcg_all_lift simp: crunch_simps)

lemma sched_context_update_consumed_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_update_consumed param_a \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace> "
  by (wpsimp simp: sched_context_update_consumed_def get_sched_context_def get_object_def)

lemma schedule_tcb_is_original_cap[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (is_original_cap s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def reschedule_required_def set_scheduler_action_def
                   tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def is_schedulable_def
                   get_sched_context_def get_object_def thread_get_def)

lemma get_sched_context_inv[wp]: "\<lbrace>P\<rbrace> get_sched_context sc_ptr \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: get_sched_context_def wp: get_object_wp)


(* this needs to be invs rule, which will required lemmas for send_ipc, handle_timeout, etc.
lemma end_timeslice_inv[wp]:
  "(\<And>s f. (P (trans_state f s) = P s)) \<Longrightarrow>
   \<lbrace>\<lambda>s. P (s\<lparr>reprogram_timer := T\<rparr>)\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>rv s. P (s\<lparr>reprogram_timer := T\<rparr>)\<rbrace>"
  by (wpsimp simp: end_timeslice_def refill_sufficient_def get_refills_def refill_ready_def
               wp: hoare_drop_imp
      | (drule_tac x = "s\<lparr>reprogram_timer := T\<rparr>" in meta_spec, simp))+
*)


(* can we say this? what about charge_budget?
lemma check_budget_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
   \<Longrightarrow> \<lbrace>P\<rbrace> check_budget \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: check_budget_def)

lemma set_refills_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
  \<Longrightarrow> \<lbrace>P\<rbrace> set_refills scp refills \<lbrace>\<lambda>rv. P\<rbrace>"
  oops

lemma charge_budget_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
   \<Longrightarrow> \<lbrace>P\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>rv. P\<rbrace>"
  oops
*)


crunches sched_context_donate
  for st_tcb_at[wp]: "\<lambda>s. Q (st_tcb_at P t s)"
  and fault_tcb_at[wp]: "\<lambda>s. Q (fault_tcb_at P t s)"
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  (wp: crunch_wps simp: crunch_simps ignore: set_tcb_obj_ref)

lemma reply_push_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t and K (t \<noteq> caller) and K (t \<noteq> callee)\<rbrace>
     reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_push_def bind_sc_reply_def update_sk_obj_ref_def get_thread_state_def
                   thread_get_def no_reply_in_ts_def comp_def
               wp: weak_if_wp sts_st_tcb_at_cases hoare_vcg_all_lift hoare_vcg_const_imp_lift
         | wp (once) hoare_drop_imp)+

lemma sched_context_update_consumed_if_live[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace>
     sched_context_update_consumed param_a
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def update_sched_context_def
                  wp: get_sched_context_wp get_object_wp)
  done

crunches
  set_irq_state, set_simple_ko
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches
  set_tcb_queue, set_irq_state, set_simple_ko, update_sk_obj_ref, do_machine_op
  for ct_in_state[wp]: "ct_in_state P"
  (wp: ct_in_state_thread_state_lift)

lemma check_budget_true:
  "\<lbrace>P\<rbrace> check_budget \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding check_budget_def
  by (wpsimp | rule hoare_drop_imp)+

lemma check_budget_restart_true:
  "\<lbrace>P\<rbrace> check_budget_restart \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding check_budget_restart_def
  apply (wpsimp wp: gts_wp hoare_vcg_all_lift)
   apply (rule hoare_drop_imp)
   apply (wpsimp wp: hoare_vcg_if_lift2 check_budget_true | rule hoare_drop_imp)+
  done

end
