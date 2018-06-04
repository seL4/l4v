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

(* FIXME - Move Invariants_AI *)
lemma invs_exst [iff]:
  "invs (trans_state f s) = invs s"
  by (simp add: invs_def valid_state_def)

lemma maybeM_inv[wp]:
  "\<forall>a. \<lbrace>P\<rbrace> f a \<lbrace>\<lambda>_. P\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> maybeM f opt \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: maybeM_def; fastforce)

crunch inv[wp]: ethread_get, ethread_get_when P

lemma get_sched_context_sp:
  "\<lbrace>P\<rbrace> get_sched_context sc_ptr
   \<lbrace> \<lambda>r s. P s \<and> (\<exists>n. ko_at (SchedContext r n) sc_ptr s)\<rbrace>"
  apply (simp add: get_sched_context_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule get_object_sp)
  apply (wpsimp, fastforce)
  done


text {* update\_sched\_context *}

lemma set_sched_context_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> set_sched_context ref sc \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: set_sched_context_def get_object_def)

lemma set_sched_context_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_sched_context ref sc \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: set_sched_context_def get_object_def)
  apply (auto simp: obj_at_def is_tcb_def)
  done

lemma set_sched_context_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> set_sched_context ref sc \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: set_sched_context_def set_object_def get_object_def valid_irq_handlers_def
                      irq_issued_def ran_def)
  apply (subgoal_tac "caps_of_state s (a, b) = Some cap")
   apply fastforce
  apply (subst cte_wp_caps_of_lift; auto simp: cte_wp_at_cases)
  done

lemma set_sched_context_valid_objs[wp]:
  "\<lbrace>\<lambda>s. valid_objs s \<and> valid_sched_context sc s\<rbrace> set_sched_context ref sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: set_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma update_sched_context_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: update_sched_context_def get_object_def)

lemma update_sched_context_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def)
  apply (auto simp: obj_at_def is_tcb_def)
  done

lemma update_sched_context_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> update_sched_context ref f \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: update_sched_context_def set_object_def get_object_def valid_irq_handlers_def
                      irq_issued_def ran_def)
  apply (subgoal_tac "caps_of_state s (a, b) = Some cap")
   apply fastforce
  apply (subst cte_wp_caps_of_lift; auto simp: cte_wp_at_cases)
  done

lemma update_sched_context_valid_objs_same:
  "\<lbrace>\<lambda>s. valid_objs s \<and> (\<forall>sc. valid_sched_context sc s \<longrightarrow> valid_sched_context (f sc) s)\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma update_sched_context_valid_objs_update:
  "\<lbrace>\<lambda>s. valid_objs s
     \<and> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                \<and> valid_sched_context (f sc) s) ref s\<rbrace>
     update_sched_context ref f \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def wp: set_object_valid_objs)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def obj_at_def)
  done

lemma refs_in_get_refs:
  "(x, ref) \<in> get_refs REF ntfn \<Longrightarrow> ref = REF"
  by (auto simp: get_refs_def split: option.splits)

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)

text {* set_sc_obj_ref/get_sc_obj_ref *}

lemma get_sc_obj_ref_inv[simp]:
  "\<lbrace>P\<rbrace> get_sc_obj_ref f t \<lbrace>\<lambda>r. P\<rbrace>"
  by (wpsimp simp: get_sc_obj_ref_def get_sched_context_def get_object_def)


crunches set_sc_obj_ref,get_sc_obj_ref
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "tcb_at t"
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
 and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
 and valid_ioc[wp]: "valid_ioc"
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
 and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
 and valid_irq_handlers[wp]: "valid_irq_handlers"
 and valid_mdb[wp]: valid_mdb
 and valid_idle[wp]: valid_idle
 and zombies[wp]: zombies_final
  (simp: Let_def wp: hoare_drop_imps)

lemma set_sc_ntfn_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound ntfn \<longrightarrow> ex_nonz_cap_to scp s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_sc_obj_ref sc_ntfn_update scp ntfn
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def
           wp: get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=scp in spec)
  apply (clarsimp simp: obj_at_def live_def live_sc_def)
  done

lemma set_sc_tcb_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound tcb \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_sc_obj_ref sc_tcb_update t tcb
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def wp: get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=t in spec)
  apply (fastforce simp: obj_at_def live_def live_sc_def)
  done

lemma set_sc_yf_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound tcb \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_sc_obj_ref sc_yield_from_update t tcb
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def wp: get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=t in spec)
  apply (fastforce simp: obj_at_def live_def live_sc_def)
  done

lemma set_sc_replies_iflive[wp]:
  "\<lbrace>\<lambda>s. (replies\<noteq>[] \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_sc_obj_ref sc_replies_update t replies
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def wp: get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=t in spec)
  apply (fastforce simp: obj_at_def live_def live_sc_def)
  done

lemma set_sc_ntfn_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_ntfn ntfn\<rbrace> set_sc_obj_ref sc_ntfn_update t ntfn \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: set_sc_obj_ref_def update_sched_context_def obj_at_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma set_sc_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_tcb ntfn\<rbrace> set_sc_obj_ref sc_tcb_update t ntfn \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: set_sc_obj_ref_def obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma set_sc_yf_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_tcb ntfn\<rbrace> set_sc_obj_ref sc_yield_from_update t ntfn \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: set_sc_obj_ref_def obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def a_type_def)
  done

lemma set_sc_replies_valid_objs[wp]:
  "\<lbrace>valid_objs and (\<lambda>s. list_all (\<lambda>rp. reply_at rp s) replies) and K (distinct replies)\<rbrace>
       set_sc_obj_ref sc_replies_update t replies \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs get_object_wp
          simp: set_sc_obj_ref_def obj_at_def update_sched_context_def
          split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_sched_context_def obj_at_def a_type_def)
  done

lemma set_sc_obj_ref_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> set_sc_obj_ref f t' ntfn \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma set_sc_ntfn_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case ntfn of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCNtfn)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCNtfn})))\<rbrace>
   set_sc_obj_ref sc_ntfn_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def set_object_def
                 wp: get_object_wp)
  apply (fastforce elim!: rsubst[where P=P]
      simp: insert_iff state_refs_of_def obj_at_def refs_of_sc_def Un_def
      split_def  Collect_eq get_refs_def2
      intro!: ext split: option.splits if_splits)
  done

lemma set_sc_tcb_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case tcb of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCTcb)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCTcb})))\<rbrace>
   set_sc_obj_ref sc_tcb_update t tcb
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def update_sched_context_def wp: get_object_wp)
  apply (fastforce elim!: rsubst[where P=P]
      simp: state_refs_of_def obj_at_def Un_def split_def  Collect_eq get_refs_def2
      intro!: ext split: option.splits if_splits)
  done

lemma set_sc_yf_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case tcb of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, SCYieldFrom)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCYieldFrom})))\<rbrace>
   set_sc_obj_ref sc_yield_from_update t tcb
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def update_sched_context_def
                wp: get_object_wp)
  apply (fastforce elim!: rsubst[where P=P]
      simp: state_refs_of_def obj_at_def Un_def
      split_def  Collect_eq get_refs_def2
      intro!: ext split: option.splits if_splits)
  done

lemma set_sc_replies_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case replies of [] \<Rightarrow> {}
                                    | _ \<Rightarrow> set (map (\<lambda>r. (r, SCReply)) replies)) \<union>
                         (state_refs_of s t - {x \<in> state_refs_of s t. snd x = SCReply})))\<rbrace>
   set_sc_obj_ref sc_replies_update t replies
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def update_sched_context_def
                wp: get_object_wp simp_del: fun_upd_apply)
  apply (fastforce elim!: rsubst[where P=P] intro!: ext
                  dest!: ko_at_state_refs_ofD split: list.splits
                  simp: get_refs_def2 state_refs_of_def image_iff conj_disj_distribR Collect_eq)
  done

text {* set_reply_obj_ref *}

crunches update_sk_obj_ref,get_sk_obj_ref
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
 and zombies[wp]: zombies_final
 and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"

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
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_reply_def)
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
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, ReplySchedContext)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = ReplySchedContext})))\<rbrace>
   set_reply_obj_ref reply_sc_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_object_def
           wp: get_sched_context_wp get_simple_ko_wp)
  apply (fastforce elim!: rsubst[where P=P]
      simp:  state_refs_of_def obj_at_def refs_of_reply_def Un_def
      split_def  Collect_eq get_refs_def2
      intro!: ext split: option.splits if_splits)
  done

lemma set_reply_tcb_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, ReplyTCB)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = ReplyTCB})))\<rbrace>
   set_reply_obj_ref reply_tcb_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_object_def
           wp: get_sched_context_wp get_simple_ko_wp)
  apply (fastforce elim!: rsubst[where P=P]
      simp:  state_refs_of_def obj_at_def refs_of_reply_def Un_def
      split_def  Collect_eq get_refs_def2
      intro!: ext split: option.splits if_splits)
  done

(* RT FIXME: Move to Invariants_AI?  *)
definition
  sc_ntfn_sc_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_ntfn_sc_at P \<equiv> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_ntfn sc))"

definition
  sc_tcb_sc_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_tcb_sc_at P \<equiv> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_tcb sc))"

definition
  sc_yf_sc_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_yf_sc_at P \<equiv> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_yield_from sc))"

definition
  sc_replies_sc_at :: "(obj_ref list \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_replies_sc_at P \<equiv> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_replies sc))"

definition
  reply_sc_reply_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "reply_sc_reply_at P \<equiv> obj_at (\<lambda>ko. \<exists>r. ko = Reply r \<and> P (reply_sc r))"

definition
  reply_tcb_reply_at :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "reply_tcb_reply_at P \<equiv> obj_at (\<lambda>ko. \<exists>r. ko = Reply r \<and> P (reply_tcb r))"

(* end: move to invariant_AI *)

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


text {* set_tcb_obj_ref/get_tcb_obj_ref *}

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

crunches set_thread_state_ext
 for aligned[wp]: pspace_aligned
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "tcb_at tptr"
 and st_tcb_at[wp]: "st_tcb_at P tptr"
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


text {* possible_switch_to invariants *}

crunches tcb_sched_action,reschedule_required,possible_switch_to,tcb_release_enqueue
 for aligned[wp]: pspace_aligned
 and it[wp]: "\<lambda>s. P (idle_thread s)"
 and distinct[wp]: pspace_distinct
 and sc_at[wp]: "sc_at sc_ptr"
 and tcb_at[wp]: "tcb_at tptr"
 and st_tcb_at[wp]: "st_tcb_at P tptr"
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
  (simp: Let_def wp: hoare_drop_imps hoare_vcg_if_lift2 mapM_wp
   ignore: set_tcb_obj_ref get_tcb_obj_ref)



text {* sched\_context\_donate and others *}

lemma sched_context_donate_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
       wp: hoare_drop_imp)

lemma sched_context_donate_irq_node[wp]:
 "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
   sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def get_object_def get_sc_obj_ref_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma sched_context_donate_interrupt_states[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
    sched_context_donate scp tcbp \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  by (wpsimp simp: sched_context_donate_def get_object_def get_sc_obj_ref_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma sched_context_donate_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def wp: hoare_drop_imp)

lemmas sched_context_donate_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF sched_context_donate_caps_of_state
                                  sched_context_donate_interrupt_states]

lemma sched_context_donate_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_object_def
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
      wp: hoare_drop_imp)

lemma sched_context_donate_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
      wp: hoare_drop_imp)

lemma sched_context_donate_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def wp: hoare_drop_imp)

lemma sched_context_donate_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def wp: hoare_drop_imp)

crunch arch [wp]: set_reply "\<lambda>s. P (arch_state s)"
  (simp: get_object_def)

lemma scheduling_context_update [iff]: (* FIXME: move it to Invariants_AI *)
  "valid_sched_context sc (trans_state f s) = valid_sched_context sc s"
  by (simp add: valid_sched_context_def valid_bound_obj_def split: option.splits)

lemma sched_context_donate_valid_objs [wp]:
  "\<lbrace>valid_objs and tcb_at tcbp\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def wp: get_sched_context_wp)
  apply (intro conjI; clarsimp simp: )
   apply (erule (1) obj_at_valid_objsE, fastforce simp: obj_at_def is_sc_obj_def valid_obj_def)+
  done

lemma sched_context_donate_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
     wp: hoare_drop_imp)

lemma sched_context_donate_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
    wp: hoare_drop_imp)

lemma sched_context_donate_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
  wp: hoare_drop_imp)

lemma sched_context_donate_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
    wp: hoare_drop_imp)

lemma sched_context_donate_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
     wp: hoare_drop_imp)

lemma sched_context_donate_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
      wp: hoare_drop_imp)

lemma sched_context_donate_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
    wp: hoare_drop_imp)

lemma sched_context_donate_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_donate scp tcbp \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma sched_context_donate_iflive[wp]:
  "\<lbrace>\<lambda>s.  if_live_then_nonz_cap s \<and>
         ex_nonz_cap_to scp s \<and>
         ex_nonz_cap_to tcbp s\<rbrace>
   sched_context_donate scp tcbp
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (unfold sched_context_donate_def)
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def get_tcb_def set_tcb_obj_ref_def is_sc_obj_def
                      obj_at_def tcb_cap_cases_def ex_cap_to_after_update get_sc_obj_ref_def
                  wp: get_sched_context_wp hoare_vcg_conj_lift weak_if_wp
                 split: kernel_object.splits option.splits |
         (subst trans_state_update[symmetric] ex_nonz_cap_to_more_update)+)+
  done

lemma sched_context_donate_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> sched_context_donate scp tcbp
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sched_context_def get_object_def get_sc_obj_ref_def
   wp: hoare_drop_imp)

text {* reply\_remove and others *}

lemma reply_remove_irq_node[wp]:
 "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
   reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def get_object_def
                   update_sk_obj_ref_def set_simple_ko_def set_object_def get_simple_ko_def
                   get_sched_context_def reply_unlink_tcb_def set_thread_state_def case_option_If2
                   get_thread_state_def thread_get_def)

lemma reply_remove_interrupt_states[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def get_object_def
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
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def update_sk_obj_ref_def
                   get_sched_context_def
               wp: hoare_drop_imp)

lemma reply_unlink_sc_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def update_sk_obj_ref_def)
       apply (wpsimp simp: set_simple_ko_def set_object_def get_simple_ko_def get_object_def
                           get_sched_context_def)+
  apply (fastforce simp: valid_obj_def valid_sched_context_def valid_reply_def valid_bound_obj_def
                         obj_at_def is_ntfn_def is_tcb_def is_reply_def list_all_iff
                  split: option.splits)
  done

lemma reply_unlink_sc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def update_sk_obj_ref_def get_simple_ko_def
                   get_object_def get_sched_context_def)

lemma reply_unlink_tcb_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def get_simple_ko_def get_object_def
                      get_thread_state_def thread_get_def)
  apply (auto simp: valid_obj_def valid_reply_def)
  done

lemma reply_unlink_tcb_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  apply  (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def obj_at_def is_tcb a_type_def
            split: kernel_object.splits wp: thread_get_wp get_object_wp get_simple_ko_wp)
     apply (rule hoare_strengthen_post)
      apply (rule gts_sp)
     apply (clarsimp simp: obj_at_def pred_tcb_at_def, fastforce)
    apply (wpsimp wp: get_simple_ko_wp)+
  apply (clarsimp simp: obj_at_def pred_tcb_at_def is_tcb)
  done

lemma reply_remove_valid_objs [wp]:
  "\<lbrace>\<lambda>s. \<exists>t. valid_objs s \<and> reply_tcb_reply_at (\<lambda>x. x=Some t \<and> tcb_at t s) r s\<rbrace>
        reply_remove r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: reply_remove_def update_sk_obj_ref_def get_simple_ko_def
                      get_thread_state_def get_sched_context_def
                  wp: hoare_vcg_if_lift2 hoare_drop_imp get_object_wp thread_get_wp)
  apply (clarsimp simp: obj_at_def reply_tcb_reply_at_def is_tcb is_reply cong: conj_cong)
  done

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
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def wp: hoare_drop_imp)

lemma reply_remove_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> reply_remove r \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_unlink_sc_def reply_unlink_tcb_def wp: hoare_drop_imp)

lemma reply_remove_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_remove r \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma reply_unlink_sc_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> reply_unlink_sc sc_ptr reply_ptr \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def set_simple_ko_def set_object_def get_object_def
                      get_simple_ko_def get_sched_context_def partial_inv_def)
  apply (intro conjI)
   apply (fastforce simp: live_def live_sc_def obj_at_def is_reply
                   elim!: ex_cap_to_after_update
                   dest!: if_live_then_nonz_capD2)
  apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def is_reply live_def live_reply_def
                  elim!: ex_cap_to_after_update)
  done

lemma reply_unlink_tcb_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> reply_unlink_tcb reply_ptr \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                   get_object_def)
  apply (clarsimp simp: a_type_def split: kernel_object.splits dest!: get_tcb_SomeD)
  by (rule conjI; drule (1) if_live_then_nonz_capD2; clarsimp simp: live_def live_reply_def)

crunch ex_nonz_cap_to[wp]: reply_unlink_tcb, reply_unlink_sc "ex_nonz_cap_to t"
  (wp: hoare_drop_imps)

lemma reply_remove_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to rp
    and (\<lambda>s. reply_tcb_reply_at (\<lambda>p. \<forall>tp. p = (Some tp) \<longrightarrow> ex_nonz_cap_to tp s) rp s)
    and (\<lambda>s. reply_sc_reply_at (\<lambda>p. \<forall>scp. p = (Some scp) \<longrightarrow> ex_nonz_cap_to scp s) rp s)\<rbrace>
   reply_remove rp
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: reply_remove_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply = None")
   apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)
  apply (case_tac "reply_sc reply = None")
   apply (rule hoare_seq_ext [OF _ assert_opt_inv])
   apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2)
  apply (wpsimp simp: obj_at_def reply_sc_reply_at_def reply_tcb_reply_at_def
                  wp: hoare_drop_imp hoare_vcg_if_lift2)
  done

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

crunches set_sched_context,update_sched_context
  for valid_irq_states[wp]: valid_irq_states

(*
crunch typ_at[wp]: postpone, sched_context_bind_tcb "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (ignore: check_cap_at setNextPC zipWithM
       wp: hoare_drop_imps mapM_x_wp' maybeM_inv select_wp
     simp: crunch_simps)
*)

lemma set_refills_empty_fail [simp]: (* move it elsewhere? *)
  "empty_fail (set_refills sc_ptr refills)"
  by (auto simp: set_refills_def get_sched_context_def update_sched_context_def get_object_def
                 set_object_is_modify
          split: kernel_object.splits)

lemma do_extended_op_empty_fail [simp]: (* move it elsewhere? *)
  "empty_fail (do_extended_op eop)"
  by (fastforce simp: do_extended_op_def empty_fail_get mk_ef_def
               intro: empty_fail_bind empty_fail_select_f)

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
crunch typ_at[wp]: get_sched_context "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv simp: get_object_def)
crunch typ_at[wp]: sched_context_unbind_yield_from "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps ignore: get_ntfn_obj_ref)

lemma sched_context_unbind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_unbind_tcb scref \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imp
           simp: sched_context_unbind_tcb_def)

crunch typ_at[wp]: unbind_from_sc, sched_context_maybe_unbind_ntfn, reply_unlink_sc,
 sched_context_clear_replies, sched_context_unbind_yield_from, sched_context_unbind_reply
 "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps simp: get_tcb_obj_ref_def ignore: get_ntfn_obj_ref)

lemma schedule_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

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
  by (wpsimp simp: postpone_def get_sc_obj_ref_def wp: dxo_wp_weak hoare_drop_imp
         | (drule_tac x="s\<lparr>reprogram_timer := True\<rparr>" in meta_spec, simp))+

(* this needs to be invs rule, which will required lemmas for send_ipc, handle_timeout, etc.
lemma end_timeslice_inv[wp]:
  "(\<And>s f. (P (trans_state f s) = P s)) \<Longrightarrow>
   \<lbrace>\<lambda>s. P (s\<lparr>reprogram_timer := T\<rparr>)\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>rv s. P (s\<lparr>reprogram_timer := T\<rparr>)\<rbrace>"
  by (wpsimp simp: end_timeslice_def refill_sufficient_def get_refills_def refill_ready_def
               wp: hoare_drop_imp
      | (drule_tac x = "s\<lparr>reprogram_timer := T\<rparr>" in meta_spec, simp))+
*)

lemma get_refills_inv[wp]: "\<lbrace>P\<rbrace> get_refills sc_ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: get_refills_def)


(* can we say this? what about charge_budget?
lemma check_budget_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
   \<Longrightarrow> \<lbrace>P\<rbrace> check_budget \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: check_budget_def)

lemma set_refills_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
  \<Longrightarrow> \<lbrace>P\<rbrace> set_refills scp refills \<lbrace>\<lambda>rv. P\<rbrace>"
  oops
  find_theorems(80) "set_object"
  thm set_object_wp

lemma charge_budget_inv[wp]: "(\<And>s f. P (trans_state f s) = P s)
   \<Longrightarrow> \<lbrace>P\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>rv. P\<rbrace>"
  oops
*)



lemma sort_queue_notin_inv: "\<lbrace>K (t \<notin> set ls) and P t\<rbrace> sort_queue ls \<lbrace>\<lambda>rv. P t\<rbrace>"
  apply (wpsimp simp: sort_queue_def wp: mapM_wp)
  apply auto
  done

lemma sched_context_donate_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def set_sc_obj_ref_def get_sc_obj_ref_def
               wp: weak_if_wp hoare_drop_imp)

lemma reply_push_st_tcb_at[wp]:
  "P (BlockedOnReply (Some reply_ptr)) \<Longrightarrow>
   \<lbrace>st_tcb_at P t and K (t \<noteq> caller) and K (t \<noteq> callee)\<rbrace>
     reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_push_def update_sk_obj_ref_def set_sc_obj_ref_def get_thread_state_def
                   thread_get_def no_reply_in_ts_def unbind_reply_in_ts_def comp_def
               wp: weak_if_wp sts_st_tcb_at_cases hoare_drop_imp)

lemma sched_context_update_consumed_if_live[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace>
  sched_context_update_consumed param_a \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def set_sched_context_def
     wp: get_sched_context_wp get_object_wp)
  by (clarsimp simp: if_live_then_nonz_cap_def obj_at_def live_def live_sc_def)
end
