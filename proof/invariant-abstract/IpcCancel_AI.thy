(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_AI
imports ArchSchedule_AI
begin

arch_requalify_facts
  arch_stit_invs
  arch_post_cap_deletion_pred_tcb_at

declare arch_post_cap_deletion_pred_tcb_at[wp]

lemma blocked_cancel_ipc_simple:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc ts t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp sts_st_tcb_at')+

lemma cancel_signal_simple:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: cancel_signal_def | wp sts_st_tcb_at')+

crunch cancel_all_ipc
  for typ_at: "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)

lemma cancel_all_helper:
  "\<lbrace>valid_objs and
    (\<lambda>s. \<forall>t \<in> set queue. st_tcb_at (\<lambda>st. \<not> halted st) t s)\<rbrace>
   mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                  tcb_sched_action tcb_sched_enqueue t od) queue
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [where S="set queue", simplified])
    apply (wpsimp wp: hoare_vcg_const_Ball_lift sts_st_tcb_at_cases)
    apply (erule(1) my_BallE)
    apply (clarsimp simp: st_tcb_def2)
    apply (frule(1) valid_tcb_objs)
    apply (clarsimp simp: valid_tcb_def valid_tcb_state_def
                          cte_wp_at_cases tcb_cap_cases_def
                   dest!: get_tcb_SomeD)
   apply simp+
  done


lemma cancel_all_ipc_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_ipc ptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, simp)
   apply (wp cancel_all_helper hoare_vcg_const_Ball_lift
        | clarsimp simp: ep_queued_st_tcb_at obj_at_def valid_ep_def)+
  done


crunch cancel_all_signals
  for typ_at: "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)


lemma unbind_notification_valid_objs_helper:
  "valid_ntfn ntfn s \<longrightarrow> valid_ntfn (ntfn_set_bound_tcb ntfn None) s "
  by (clarsimp simp: valid_bound_tcb_def valid_ntfn_def
                  split: option.splits ntfn.splits)

lemma unbind_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  unfolding unbind_notification_def
  apply (wp thread_set_valid_objs_triv set_simple_ko_valid_objs hoare_drop_imp | wpc
         | simp add: tcb_cap_cases_def
         | strengthen unbind_notification_valid_objs_helper)+
   apply (wp thread_get_wp' | simp add:get_bound_notification_def)+
   apply (clarsimp)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp:valid_obj_def valid_tcb_def)+
  done


lemma cancel_all_signals_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_signals ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: cancel_all_signals_def unbind_maybe_notification_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp unbind_notification_valid_objs | wpc | simp_all add:unbind_maybe_notification_def)+
    apply (wp cancel_all_helper hoare_vcg_const_Ball_lift
             set_simple_ko_valid_objs unbind_notification_valid_objs
        | clarsimp simp: ntfn_queued_st_tcb_at obj_at_def
                         valid_ntfn_def valid_bound_tcb_def
        | wpc)+
  apply (clarsimp split: option.splits)
  apply (erule (1) valid_objsE)
  apply (simp add: valid_obj_def valid_ntfn_def)
  done


lemma get_ep_queue_inv[wp]:
  "\<lbrace>P\<rbrace> get_ep_queue ep \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases ep, simp_all add: get_ep_queue_def)


lemma cancel_all_ipc_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cancel_all_ipc_def
  by (wp ep_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases | simp)+


lemmas cancel_all_ipc_makes_simple[wp] =
  cancel_all_ipc_st_tcb_at[where P=simple, simplified]


lemma unbind_notification_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_notification t' \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding unbind_notification_def
  by (wp thread_set_no_change_tcb_state hoare_drop_imps | wpc | simp)+


lemma unbind_maybe_notification_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_maybe_notification r \<lbrace>\<lambda>rv. st_tcb_at P t \<rbrace>"
  unfolding unbind_maybe_notification_def
  apply (rule hoare_pre)
  apply (wp  thread_set_no_change_tcb_state hoare_drop_imps| wpc | simp)+
  done

lemma cancel_all_signals_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cancel_all_signals_def unbind_maybe_notification_def
  by (wp ntfn_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases
         hoare_drop_imps unbind_notification_st_tcb_at
    | simp | wpc)+


lemmas cancel_all_signals_makes_simple[wp] =
       cancel_all_signals_st_tcb_at[where P=simple, simplified]




lemma get_blocking_object_inv[wp]:
  "\<lbrace>P\<rbrace> get_blocking_object st \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases st, simp_all add: get_blocking_object_def)


lemma blocked_ipc_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> P Structures_A.Inactive)\<rbrace>
     blocked_cancel_ipc st t
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp sts_st_tcb_at_cases hoare_weak_lift_imp, simp+)
  done


lemma cancel_signal_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> (P Structures_A.Running \<and> P Structures_A.Inactive))\<rbrace>
     cancel_signal t ntfn
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wp sts_st_tcb_at_cases ntfn_cases_weak_wp hoare_weak_lift_imp)
  apply simp
  done


lemma fast_finalise_misc[wp]:
"\<lbrace>st_tcb_at simple t \<rbrace> fast_finalise a b \<lbrace>\<lambda>_. st_tcb_at simple t\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp|clarsimp)+
  done

locale IpcCancel_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_post_cap_deletion_typ_at[wp]:
      "\<And>P T p acap. \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
    assumes arch_post_cap_deletion_idle_thread[wp]:
      "\<And>P acap. \<lbrace>\<lambda>(s :: 'a state). P (idle_thread s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"

crunch update_restart_pc
  for typ_at[wp]: "\<lambda>s. P (typ_at ty ptr s)"
  (* NB: Q needed for following has_reply_cap proof *)
  and cte_wp_at[wp]: "\<lambda>s. Q (cte_wp_at P cte s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and pred_tcb_at[wp]: "\<lambda>s. pred_tcb_at P proj tcb s"
  and invs[wp]: "\<lambda>s. invs s"

lemma update_restart_pc_has_reply_cap[wp]:
  "\<lbrace>\<lambda>s. \<not> has_reply_cap t s\<rbrace> update_restart_pc t \<lbrace>\<lambda>_ s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: has_reply_cap_def)
  apply (wp hoare_vcg_all_lift)
  done

crunch reply_cancel_ipc
  for st_tcb_at_simple[wp]: "st_tcb_at simple t"
  (wp: crunch_wps sts_st_tcb_at_cases thread_set_no_change_tcb_state
   simp: crunch_simps unless_def)

lemma cancel_ipc_simple [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule bind_wp [OF _ gts_sp])
  apply (case_tac state, simp_all)
         apply (wp hoare_strengthen_post [OF blocked_cancel_ipc_simple]
                   hoare_strengthen_post [OF cancel_signal_simple]
                   hoare_strengthen_post
                      [OF reply_cancel_ipc_st_tcb_at_simple [where t=t]]
                   sts_st_tcb_at_cases
                   hoare_drop_imps
                        | clarsimp elim!: pred_tcb_weakenE pred_tcb_at_tcb_at)+
  done

lemma blocked_cancel_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> blocked_cancel_ipc st t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def get_blocking_object_def get_ep_queue_def
                   get_simple_ko_def)
  apply (wp get_object_wp|wpc)+
  apply simp
  done


lemma blocked_cancel_ipc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc st t' \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

context IpcCancel_AI begin

crunch cancel_ipc, reply_cancel_ipc, unbind_maybe_notification
  for typ_at[wp]: "\<lambda>(s :: 'a state). P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE
     simp: crunch_simps unless_def)

lemma cancel_ipc_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> cancel_ipc t' \<lbrace>\<lambda>rv. (tcb_at t) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

lemma gbep_ret:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr pl' \<or>
     st = Structures_A.BlockedOnSend epPtr pl \<rbrakk> \<Longrightarrow>
  get_blocking_object st = return epPtr"
  by (auto simp add: get_blocking_object_def)


lemma st_tcb_at_valid_st2:
  "\<lbrakk> st_tcb_at ((=) st) t s; valid_objs s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def get_tcb_def pred_tcb_at_def
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done


definition
 "emptyable \<equiv> \<lambda>p s. (tcb_at (fst p) s \<and> snd p = tcb_cnode_index 2) \<longrightarrow>
                          st_tcb_at halted (fst p) s"

locale delete_one_abs = IpcCancel_AI state_ext
  for state_ext :: "('a :: state_ext) itself" +
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs and emptyable p\<rbrace> (cap_delete_one p :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"

  assumes delete_one_deletes:
    "\<lbrace>\<top>\<rbrace> (cap_delete_one sl :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"

  assumes delete_one_caps_of_state:
    "\<And>P p. \<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
                  \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
             (cap_delete_one p :: (unit,'a) s_monad)
            \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"


lemma reply_master_no_descendants_no_reply:
  "\<lbrakk> valid_mdb s; valid_reply_masters s; tcb_at t s \<rbrakk> \<Longrightarrow>
   descendants_of (t, tcb_cnode_index 2) (cdt s) = {} \<longrightarrow> \<not> has_reply_cap t s"
  by (fastforce simp: invs_def valid_state_def valid_mdb_def has_reply_cap_def
                     cte_wp_at_caps_of_state reply_mdb_def is_reply_cap_to_def
                     reply_caps_mdb_def descendants_of_def cdt_parent_defs
               dest: reply_master_caps_of_stateD tranclD)


lemma reply_cap_unique_descendant:
  "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow>
   \<forall>sl\<in>descendants_of (t, tcb_cnode_index 2) (cdt s).  \<forall>sl'. sl' \<noteq> sl \<longrightarrow>
      sl' \<notin> descendants_of (t, tcb_cnode_index 2) (cdt s)"
  apply (subgoal_tac "cte_wp_at (\<lambda>c. (is_master_reply_cap c \<and> obj_ref_of c = t)
                                     \<or> c = cap.NullCap)
                                (t, tcb_cnode_index 2) s")
   apply (clarsimp simp: invs_def valid_state_def valid_mdb_def2 is_cap_simps
                         valid_reply_caps_def cte_wp_at_caps_of_state)
   apply (erule disjE)
    apply (fastforce simp: reply_mdb_def is_cap_simps dest: unique_reply_capsD)
   apply (fastforce dest: mdb_cte_at_Null_descendants)
  apply (clarsimp simp: tcb_cap_wp_at invs_valid_objs
                        tcb_cap_cases_def is_cap_simps)
  done


lemma reply_master_one_descendant:
  "\<lbrakk> invs s; tcb_at t s; descendants_of (t, tcb_cnode_index 2) (cdt s) \<noteq> {} \<rbrakk>
   \<Longrightarrow> \<exists>sl. descendants_of (t, tcb_cnode_index 2) (cdt s) = {sl}"
  by (fastforce elim: construct_singleton dest: reply_cap_unique_descendant)


lemma ep_redux_simps2:
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   valid_ep (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
            | a # list \<Rightarrow> update_ep_queue ep xs)
     = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                   | a # list \<Rightarrow> update_ep_queue ep xs)
     = (set xs \<times> {case ep of Structures_A.SendEP xs \<Rightarrow> EPSend | Structures_A.RecvEP xs \<Rightarrow> EPRecv})"
 by (cases ep, simp_all cong: list.case_cong add: ep_redux_simps)+


lemma gbi_ep_sp:
  "\<lbrace>P\<rbrace>
     get_blocking_object st
   \<lbrace>\<lambda>ep. P and K ((\<exists>d. st = Structures_A.BlockedOnReceive ep d)
                    \<or> (\<exists>d. st = Structures_A.BlockedOnSend ep d))\<rbrace>"
  apply (cases st, simp_all add: get_blocking_object_def)
   apply (wp | simp)+
  done


lemma get_epq_sp:
  "\<lbrace>P\<rbrace>
  get_ep_queue ep
  \<lbrace>\<lambda>q. P and K (ep \<in> {Structures_A.SendEP q, Structures_A.RecvEP q})\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (cases ep)
  apply (wp|simp)+
  done

lemma refs_in_tcb_bound_refs:
  "(x, ref) \<in> tcb_bound_refs ntfn \<Longrightarrow> ref = TCBBound"
  by (auto simp: tcb_bound_refs_def split: option.splits)

lemma refs_in_ntfn_bound_refs:
  "(x, ref) \<in> ntfn_bound_refs tcb \<Longrightarrow> ref = NTFNBound"
  by (auto simp: ntfn_bound_refs_def split: option.splits)

lemma blocked_cancel_ipc_invs:
  "\<lbrace>invs and st_tcb_at ((=) st) t\<rbrace> blocked_cancel_ipc st t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (rule bind_wp [OF _ gbi_ep_sp])
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule bind_wp [OF _ get_epq_sp])
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle)
   apply (simp add: valid_tcb_state_def)
   apply (strengthen reply_cap_doesnt_exist_strg)
   apply simp
   apply (wp valid_irq_node_typ)
  apply (subgoal_tac "ep \<noteq> Structures_A.IdleEP")
   apply (clarsimp simp: ep_redux_simps2 cong: if_cong)
   apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
   apply (frule ko_at_state_refs_ofD)
   apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def)
   apply (frule st_tcb_at_state_refs_ofD)
   apply (subgoal_tac "epptr \<notin> set (remove1 t queue)")
    subgoal for epptr ep queue s
    apply (case_tac ep; simp add: valid_ep_def)
     by (timeit \<open>auto elim!: delta_sym_refs pred_tcb_weaken_strongerE
                       simp: obj_at_def is_ep_def2 idle_not_queued refs_in_tcb_bound_refs
                       dest: idle_no_refs
                      split: if_split_asm\<close>) (* slow: ~100s *)
   apply (case_tac ep, simp_all add: valid_ep_def)[1]
    apply (clarsimp, drule(1) bspec, clarsimp simp: obj_at_def is_tcb_def)+
  apply fastforce
  done

lemma symreftype_inverse':
  "symreftype ref = ref' \<Longrightarrow> ref = symreftype ref'"
  by (cases ref) simp_all

lemma cancel_signal_invs:
  "\<lbrace>invs and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfn)) t\<rbrace>
  cancel_signal t ntfn
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_signal_def
                   invs_def valid_state_def valid_pspace_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfna", simp_all)[1]
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle
           | simp add: valid_tcb_state_def
           | strengthen reply_cap_doesnt_exist_strg
           | wpc)+
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong if_cong)
  apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (case_tac ntfna)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp split:option.split)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)+
   apply (fastforce dest: refs_in_tcb_bound_refs refs_in_ntfn_bound_refs symreftype_inverse')
  apply (fastforce simp: obj_at_def is_ntfn idle_not_queued
                   dest: idle_no_refs elim: pred_tcb_weakenE)
  done

lemma reply_mdb_cte_at_master_None:
  "\<lbrakk> reply_mdb m cs; mdb_cte_at (\<lambda>p. \<exists>c. cs p = Some c \<and> cap.NullCap \<noteq> c) m;
     cs ptr = Some cap; is_master_reply_cap cap \<rbrakk> \<Longrightarrow>
    m ptr = None"
  unfolding reply_mdb_def reply_masters_mdb_def
  by (fastforce simp: is_cap_simps)


lemma reply_slot_not_descendant:
  "\<And>ptr. \<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow>
   (t, tcb_cnode_index 2) \<notin> descendants_of ptr (cdt s)"
  apply (subgoal_tac "cte_wp_at (\<lambda>c. is_master_reply_cap c \<or> c = cap.NullCap)
                                (t, tcb_cnode_index 2) s")
   apply (fastforce simp: invs_def valid_state_def valid_mdb_def2
                         cte_wp_at_caps_of_state
                   dest: reply_mdb_cte_at_master_None mdb_cte_at_Null_None
                         descendants_of_NoneD)
  apply (clarsimp simp: tcb_cap_wp_at invs_valid_objs
                        tcb_cap_cases_def)
  done

lemma reply_cancel_ipc_invs:
  assumes delete: "\<And>p. \<lbrace>invs and emptyable p\<rbrace>
                        (cap_delete_one p :: (unit,'z::state_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  shows           "\<lbrace>invs\<rbrace> (reply_cancel_ipc t :: (unit,'z::state_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (wp delete)
  apply (rule_tac Q'="\<lambda>rv. invs" in hoare_post_imp)
   apply (fastforce simp: emptyable_def dest: reply_slot_not_descendant)
  apply (wp thread_set_invs_trivial)
   apply (auto simp: tcb_cap_cases_def)+
  done


lemma (in delete_one_abs) cancel_ipc_invs[wp]:
  "\<lbrace>invs\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule bind_wp [OF _ gts_sp])
  apply (case_tac state, simp_all)
        apply (auto intro!: hoare_weaken_pre [OF return_wp]
                            hoare_weaken_pre [OF blocked_cancel_ipc_invs]
                            hoare_weaken_pre [OF cancel_signal_invs]
                            hoare_weaken_pre [OF reply_cancel_ipc_invs]
                            delete_one_invs
                     elim!: pred_tcb_weakenE)
  done

context IpcCancel_AI begin

lemma cancel_ipc_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cancel_ipc p \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma cancel_ipc_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. (cte_at p) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cte_at_typ)

end

lemma valid_ep_queue_subset:
  "\<lbrace>\<lambda>s. valid_ep ep s\<rbrace>
     get_ep_queue ep
   \<lbrace>\<lambda>queue s. valid_ep (case (remove1 t queue) of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                       | a # list \<Rightarrow> update_ep_queue ep (remove1 t queue)) s\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (case_tac ep, simp_all)
   apply wp
   apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  apply wp
  apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  done

lemma blocked_cancel_ipc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> blocked_cancel_ipc st t \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp get_simple_ko_valid[where f=Endpoint, simplified valid_ep_def2[symmetric]]
            valid_ep_queue_subset
         | simp only: valid_inactive simp_thms
                cong: imp_cong
         | rule hoare_drop_imps
         | clarsimp)+
  done


lemma cancel_signal_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> cancel_signal t ntfnptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp set_simple_ko_valid_objs
       | simp only: valid_inactive
       | simp
       | wpc)+
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (auto split: option.splits list.splits)
  done


lemma tcb_in_valid_state:
  "\<lbrakk> st_tcb_at P t s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>st. P st \<and> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def pred_tcb_at_def obj_at_def)
  apply (erule my_BallE, erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  apply blast
  done


lemma no_refs_simple_strg:
  "st_tcb_at simple t s \<and> P {} \<longrightarrow> st_tcb_at (\<lambda>st. P (tcb_st_refs_of st)) t s"
  by (fastforce elim!: pred_tcb_weakenE)+


crunch cancel_all_ipc
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: unless_def crunch_simps)

crunch cancel_all_signals, fast_finalise, unbind_notification
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: unless_def crunch_simps)

context IpcCancel_AI begin

crunch reply_cancel_ipc
  for it[wp]: "\<lambda>(s::'a state). P (idle_thread s)"
  (wp: crunch_wps simp: unless_def crunch_simps)

crunch cancel_ipc
  for it[wp]: "\<lambda>(s :: 'a state). P (idle_thread s)"

end

lemma reply_cap_descends_from_master:
  "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow>
   \<forall>sl\<in>descendants_of (t, tcb_cnode_index 2) (cdt s).  \<forall>sl' R. sl' \<noteq> sl \<longrightarrow>
      caps_of_state s sl' \<noteq> Some (cap.ReplyCap t False R)"
  apply (subgoal_tac "cte_wp_at (\<lambda>c. (is_master_reply_cap c \<and> obj_ref_of c = t)
                                     \<or> c = cap.NullCap)
                                (t, tcb_cnode_index 2) s")
   apply (clarsimp simp: invs_def valid_state_def valid_mdb_def2 is_cap_simps
                         valid_reply_caps_def cte_wp_at_caps_of_state)
   apply (erule disjE)
    apply (unfold reply_mdb_def reply_masters_mdb_def)[1]
    apply (elim conjE)
    apply (erule_tac x="(t, tcb_cnode_index 2)" in allE)
    apply (erule_tac x=t in allE)+
    apply (fastforce simp: unique_reply_caps_def is_cap_simps)
   apply (fastforce dest: mdb_cte_at_Null_descendants)
  apply (clarsimp simp: tcb_cap_wp_at invs_valid_objs
                        tcb_cap_cases_def is_cap_simps)
  done


lemma (in delete_one_abs) reply_cancel_ipc_no_reply_cap[wp]:
  notes hoare_pre
  shows "\<lbrace>invs and tcb_at t\<rbrace> (reply_cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply wp
        apply (rule_tac Q'="\<lambda>rvp s. cte_wp_at (\<lambda>c. c = cap.NullCap) rv s \<and>
                                (\<forall>sl R. sl \<noteq> rv \<longrightarrow>
                                  caps_of_state s sl \<noteq> Some (cap.ReplyCap t False R))"
                  in hoare_strengthen_post)
         apply (wp hoare_vcg_conj_lift hoare_vcg_all_lift
                   delete_one_deletes delete_one_caps_of_state)
        apply (clarsimp simp: has_reply_cap_def cte_wp_at_caps_of_state is_reply_cap_to_def)
        apply (case_tac "(aa, ba) = (a, b)",simp_all)[1]
       apply (wp hoare_vcg_all_lift | simp del: split_paired_All)+
   apply (rule_tac Q'="\<lambda>_ s. invs s \<and> tcb_at t s" in hoare_post_imp)
    apply (erule conjE)
    apply (frule(1) reply_cap_descends_from_master)
    apply (auto dest: reply_master_no_descendants_no_reply[rotated -1])[1]
   apply (wp thread_set_invs_trivial | clarsimp simp: tcb_cap_cases_def)+
  done


lemma (in delete_one_abs) cancel_ipc_no_reply_cap[wp]:
  shows "\<lbrace>invs and tcb_at t\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (wpsimp wp: hoare_post_imp [OF invs_valid_reply_caps]
                  reply_cancel_ipc_no_reply_cap
                  cancel_signal_invs cancel_signal_st_tcb_at_general
                  blocked_cancel_ipc_invs blocked_ipc_st_tcb_at_general
        | strengthen reply_cap_doesnt_exist_strg)+
   apply (rule_tac Q'="\<lambda>rv. st_tcb_at ((=) rv) t and invs" in hoare_strengthen_post)
    apply (wpsimp wp: gts_st_tcb)
   apply (fastforce simp: invs_def valid_state_def st_tcb_at_tcb_at
                   elim!: pred_tcb_weakenE)+
  done

lemma tcb_sched_action_invs[wp]:
  "\<lbrace>invs\<rbrace> tcb_sched_action action thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def)

lemma (in delete_one_abs) suspend_invs[wp]:
  "\<lbrace>invs and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   (suspend t :: (unit,'a) s_monad)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wp sts_invs_minor user_getreg_inv as_user_invs sts_invs_minor cancel_ipc_invs
         cancel_ipc_no_reply_cap
     | strengthen no_refs_simple_strg
     | simp add: suspend_def)+

context IpcCancel_AI begin

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>(s::'a state). P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: suspend_def)

lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)

lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. (tcb_at t')  :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

declare if_cong [cong del]


crunch blocked_cancel_ipc
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps)

crunch cancel_signal
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps)

locale delete_one_pre =
  fixes state_ext_type :: "('a :: state_ext) itself"
  assumes delete_one_cte_wp_at_preserved:
    "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
     \<lbrace>cte_wp_at P sl\<rbrace> (cap_delete_one sl' :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"

lemma (in delete_one_pre) reply_cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (reply_cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wpsimp wp: delete_one_cte_wp_at_preserved)
   apply (rule_tac Q'="\<lambda>_. cte_wp_at P p" in hoare_post_imp, clarsimp)
   apply (wpsimp wp: thread_set_cte_wp_at_trivial simp: ran_tcb_cap_cases)
  apply assumption
  done


lemma (in delete_one_pre) cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_pre)
   apply (wp reply_cancel_ipc_cte_wp_at_preserved | wpcw | simp)+
  done

lemma (in delete_one_pre) suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,'a) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def) (wpsimp wp: cancel_ipc_cte_wp_at_preserved)+


(* FIXME - eliminate *)
lemma obj_at_exst_update:
  "obj_at P p (trans_state f s) = obj_at P p s"
  by (rule more_update.obj_at_update)


lemma set_thread_state_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def set_object_def get_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunch cancel_all_ipc, empty_slot, is_final_cap, get_cap
  for bound_tcb_at[wp]: "bound_tcb_at P t"
  (wp: mapM_x_wp_inv)


lemma fast_finalise_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>tt b R. cap = ReplyCap tt b R) \<rbrace> fast_finalise cap final \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (case_tac cap, simp_all)


lemma get_cap_reply_cap_helper:
  "\<lbrace>\<lambda>s. \<exists>t b R. Some (ReplyCap t b R) = caps_of_state s slot \<rbrace> get_cap slot \<lbrace>\<lambda>rv s. \<exists>t b R. rv = ReplyCap t b R\<rbrace>"
  by (auto simp: valid_def get_cap_caps_of_state[symmetric])


lemma cap_delete_one_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>t b R. caps_of_state s c = Some (ReplyCap t b R)) \<rbrace>
     cap_delete_one c
   \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  apply (clarsimp simp: unless_def cap_delete_one_def)
  apply (wp fast_finalise_bound_tcb_at)
  apply (wp hoare_vcg_if_lift2, simp)
  apply (wp hoare_conjI)
   apply (wp only:hoare_drop_imp)
   apply (wp hoare_vcg_conj_lift)
   apply (wp get_cap_reply_cap_helper hoare_drop_imp | clarsimp)+
  done


lemma valid_mdb_impl_reply_masters:
  "valid_mdb s \<Longrightarrow> reply_masters_mdb (cdt s) (caps_of_state s)"
  by (auto simp: valid_mdb_def reply_mdb_def)


lemma caps_of_state_tcb_index_trans:
  "\<lbrakk>get_tcb p s = Some tcb \<rbrakk> \<Longrightarrow> caps_of_state s (p, tcb_cnode_index n) = (tcb_cnode_map tcb) (tcb_cnode_index n)"
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: caps_of_state_def)
  apply (safe)
   apply (clarsimp simp: get_object_def get_cap_def)
   apply (simp add:set_eq_iff)
   apply (drule_tac x=cap in spec)
   apply (drule_tac x=s in spec)
   apply (clarsimp simp: in_monad)
  apply (clarsimp simp: get_cap_def get_object_def)
  apply (rule ccontr)
  apply (drule not_sym)
  apply (auto simp: set_eq_iff in_monad)
  done


lemma descendants_of_nullcap:
  "\<lbrakk>descendants_of (a, b) (cdt s) \<noteq> {}; valid_mdb s \<rbrakk> \<Longrightarrow> caps_of_state s (a, b) \<noteq> Some NullCap"
  apply clarsimp
  apply (drule_tac cs="caps_of_state s" and p="(a,b)" and m="(cdt s)" in mdb_cte_at_Null_descendants)
   apply (clarsimp simp: valid_mdb_def2)+
  done

lemma reply_cancel_ipc_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t and valid_mdb and valid_objs and tcb_at p \<rbrace>
    reply_cancel_ipc p
   \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wpsimp wp: cap_delete_one_bound_tcb_at select_inv)
   apply (rule_tac Q'="\<lambda>_. bound_tcb_at P t and valid_mdb and valid_objs and tcb_at p" in hoare_strengthen_post)
    apply (wpsimp wp: thread_set_no_change_tcb_pred thread_set_mdb)
     apply (fastforce simp:tcb_cap_cases_def)
    apply (wpsimp wp: thread_set_valid_objs_triv simp: ran_tcb_cap_cases)
   apply clarsimp
   apply (frule valid_mdb_impl_reply_masters)
   apply (clarsimp simp: reply_masters_mdb_def)
   apply (spec p)
   apply (spec "tcb_cnode_index 2")
   apply (spec p)
   apply (clarsimp simp:tcb_at_def)
   apply (frule(1) valid_tcb_objs)
   apply (clarsimp simp: valid_tcb_def)
   apply (erule impE)
    apply (simp add: caps_of_state_tcb_index_trans tcb_cnode_map_def)
    apply (clarsimp simp: tcb_cap_cases_def is_master_reply_cap_def split:cap.splits  )
    apply (subgoal_tac "descendants_of (p, tcb_cnode_index 2) (cdt s) \<noteq> {}")
     prefer 2
     apply simp
    apply (drule descendants_of_nullcap, simp)
    apply (simp add: caps_of_state_tcb_index_trans tcb_cnode_map_def)
   apply fastforce
  apply simp
  done

crunch cancel_ipc
  for bound_tcb_at[wp]: "bound_tcb_at P t"
  (ignore: set_object thread_set wp: mapM_x_wp_inv)

crunch tcb_sched_action
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

context IpcCancel_AI begin
lemma suspend_unlive:
  "\<lbrace>\<lambda>(s::'a state).
      (bound_tcb_at ((=) None) t and valid_mdb and valid_objs) s \<rbrace>
   suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  apply (simp add: suspend_def set_thread_state_def set_object_def get_object_def)
    (* avoid creating two copies of obj_at *)
  supply hoare_vcg_if_split[wp_split del] if_split[split del]
  apply (wp | simp only: obj_at_exst_update)+
     apply (simp add: obj_at_def)
     apply (rule_tac Q'="\<lambda>_. bound_tcb_at ((=) None) t" in hoare_strengthen_post)
      supply hoare_vcg_if_split[wp_split]
      apply wp
     apply (auto simp: pred_tcb_def2)[1]
    apply (simp flip: if_split)
    apply wpsimp+
  apply (simp add: pred_tcb_at_tcb_at)
  done
end

definition bound_refs_of_tcb :: "'a state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> reftype) set"
where
  "bound_refs_of_tcb s t \<equiv> case kheap s t of
                              Some (TCB tcb) \<Rightarrow> tcb_bound_refs (tcb_bound_notification tcb)
                            | _ \<Rightarrow> {}"

crunch tcb_sched_action, possible_switch_to
  for valid_reply_caps[wp]: valid_reply_caps
  and valid_reply_masters[wp]: valid_reply_masters

lemma cancel_all_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then {r \<in> state_refs_of s x. snd r = TCBBound}
                                  else state_refs_of s x)
                  \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x)
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s))\<rbrace>
   mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                  tcb_sched_action tcb_sched_enqueue t od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2, wpsimp)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle sts_st_tcb_at_cases)
  apply (strengthen reply_cap_doesnt_exist_strg)
  by (auto simp: valid_tcb_state_def idle_no_ex_cap o_def if_split_asm
          elim!: rsubst[where P=sym_refs] st_tcb_weakenE)

lemma ep_no_bound_refs:
  "ep_at p s \<Longrightarrow> {r \<in> state_refs_of s p. snd r = TCBBound} = {}"
  by (clarsimp simp: obj_at_def state_refs_of_def refs_of_def is_ep ep_q_refs_of_def split: endpoint.splits)

lemma obj_at_conj_distrib:
  "obj_at (\<lambda>ko. P ko \<and> Q ko) p s \<Longrightarrow> obj_at (\<lambda>ko. P ko) p s \<and> obj_at (\<lambda>ko. Q ko) p s"
  by (auto simp:obj_at_def)

lemma ep_q_refs_of_no_ntfn_bound:
  "(x, tp) \<in> ep_q_refs_of ep \<Longrightarrow> tp \<noteq> NTFNBound"
  by (auto simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ep_q_refs_of ep"
  by (clarsimp simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_list_tcb_at:
  "\<lbrakk>ep_at p s; valid_objs s; state_refs_of s p = set q \<times> {k}; x \<in> set q \<rbrakk> \<Longrightarrow> tcb_at x s"
  apply (erule (1) obj_at_valid_objsE)
  apply (fastforce simp:is_ep valid_obj_def valid_ep_def state_refs_of_def split:endpoint.splits)
  done

lemma tcb_at_no_ntfn_bound:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, NTFNBound) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
           simp: state_refs_of_def is_tcb valid_obj_def tcb_bound_refs_def tcb_st_refs_of_def
           split:thread_state.splits option.splits)

lemma ep_no_ntfn_bound:
  "\<lbrakk>is_ep ko; refs_of ko = set q \<times> {NTFNBound}; y \<in> set q \<rbrakk> \<Longrightarrow> False"
  apply (subst (asm) set_eq_iff)
  apply (drule_tac x="(y, NTFNBound)" in spec)
  apply (clarsimp simp: refs_of_rev is_ep)
  done

lemma set_scheduler_action_invs[wp]:
  "set_scheduler_action action \<lbrace>invs\<rbrace>"
  apply (wpsimp simp: set_scheduler_action_def)
  apply (clarsimp simp: invs_def valid_state_def)
  done

crunch possible_switch_to
  for invs[wp]: invs

lemma cancel_all_ipc_invs_helper:
  assumes x: "\<And>x ko. (x, symreftype k) \<in> refs_of ko
                \<Longrightarrow> (refs_of ko = {(x, symreftype k)} \<or>
                          (\<exists>y. refs_of ko = {(x, symreftype k), (y, TCBBound)}))"
  shows
  "\<lbrace>invs and obj_at (\<lambda>ko. is_ep ko \<and> refs_of ko = set q \<times> {k}) p\<rbrace>
     do y \<leftarrow> set_endpoint p Structures_A.endpoint.IdleEP;
        y \<leftarrow> mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                           tcb_sched_action tcb_sched_enqueue t od) q;
        reschedule_required
    od \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (subst bind_assoc[symmetric])
  apply (rule bind_wp)
   apply wpsimp
  apply (rule hoare_pre)
   apply (wp cancel_all_invs_helper hoare_vcg_const_Ball_lift valid_irq_node_typ)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_ep_def live_def)
  apply (rule conjI)
   apply (fastforce simp: live_def is_ep_def elim!: obj_at_weakenE split: kernel_object.splits)
  apply (rule conjI)
   apply clarsimp
   apply (drule(1) sym_refs_obj_atD, clarsimp)
   apply (drule(1) bspec, erule(1) if_live_then_nonz_capD)
   apply (rule refs_of_live, clarsimp)
  apply (rule conjI[rotated])
   apply (subgoal_tac "\<exists>ep. ko_at (Endpoint ep) p s", clarsimp)
    apply (subgoal_tac "\<exists>rt. (x, rt) \<in> ep_q_refs_of ep", clarsimp)
     apply (fastforce elim!: ep_queued_st_tcb_at)
    apply (clarsimp simp: obj_at_def is_ep_def)+
   apply (case_tac ko, simp_all)
  apply (frule(1) sym_refs_obj_atD)
  apply (frule obj_at_state_refs_ofD)
  apply (clarsimp dest!:obj_at_conj_distrib)
  apply (thin_tac "obj_at (\<lambda>ko. refs_of ko = set q \<times> {k}) p s")
  apply (erule delta_sym_refs)
   apply (clarsimp simp: if_split_asm)+
  apply (safe)
          apply (fastforce dest!:symreftype_inverse' ep_no_ntfn_bound)
         apply (clarsimp dest!: symreftype_inverse')
         apply (frule (3) ep_list_tcb_at)
         apply (frule_tac t=y in tcb_at_no_ntfn_bound, simp+)[1]
        apply simp
       subgoal
         apply (clarsimp dest!: symreftype_inverse')
         apply (frule (3) ep_list_tcb_at)
         by (clarsimp simp: obj_at_def is_tcb is_ep)
      apply (fastforce dest!: obj_at_state_refs_ofD x)
     apply (fastforce dest!: obj_at_state_refs_ofD x)
    apply (fastforce dest!: symreftype_inverse' ep_no_ntfn_bound)
   apply (clarsimp)
  apply (fastforce dest!: symreftype_inverse' ep_no_ntfn_bound)
  done

lemma cancel_all_ipc_invs:
  "\<lbrace>invs\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, fastforce)
   apply (rule hoare_pre, rule cancel_all_ipc_invs_helper[where k=EPSend])
    apply (fastforce simp: refs_of_rev tcb_bound_refs_def split: option.splits)
   apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  apply (rule hoare_pre, rule cancel_all_ipc_invs_helper[where k=EPRecv])
   apply (fastforce simp: refs_of_rev tcb_bound_refs_def split: option.splits)
  apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  done

lemma ntfn_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma ntfn_q_refs_no_TCBBound:
  "(x, TCBBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma ntfn_bound_tcb_get_set[simp]:
  "ntfn_bound_tcb (ntfn_set_bound_tcb ntfn ntfn') = ntfn'"
  by auto

lemma ntfn_obj_tcb_get_set[simp]:
  "ntfn_obj (ntfn_set_bound_tcb ntfn ntfn') = ntfn_obj ntfn"
  by auto

lemma valid_ntfn_set_bound_None:
  "valid_ntfn ntfn s \<Longrightarrow> valid_ntfn (ntfn_set_bound_tcb ntfn None) s"
  by (auto simp: valid_ntfn_def split:ntfn.splits)

lemma ntfn_bound_tcb_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    ntfn_bound_tcb ntfn = Some tcbptr; P (Some ntfnptr)\<rbrakk>
  \<Longrightarrow> bound_tcb_at P tcbptr s"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (fastforce simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                         state_refs_of_def refs_of_rev
                   simp del: refs_of_simps)
  done

lemma bound_tcb_bound_notification_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    bound_tcb_at (\<lambda>ptr. ptr = (Some ntfnptr)) tcbptr s \<rbrakk>
  \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr"
  apply (drule_tac x=tcbptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def pred_tcb_at_def obj_at_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps)
  done

lemma unbind_notification_invs:
  shows "\<lbrace>invs\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unbind_notification_def invs_def valid_state_def valid_pspace_def)
  apply (rule bind_wp [OF _ gbn_sp])
  apply (case_tac ntfnptr, clarsimp, wp, simp)
  apply clarsimp
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs
         | clarsimp split del: if_split)+
  apply (intro conjI impI;
    (match conclusion in "sym_refs r" for r \<Rightarrow> \<open>-\<close>
        | auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: live_def valid_ntfn_set_bound_None is_ntfn valid_obj_def
    )?)
  apply (clarsimp simp: if_split)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def is_tcb
                   dest!: pred_tcb_at_tcb_at ko_at_state_refs_ofD
                   split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (frule pred_tcb_at_tcb_at)
   apply (frule_tac p=t in obj_at_ko_at, clarsimp)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (fastforce simp: obj_at_def is_tcb ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound refs_of_rev
                          tcb_ntfn_is_bound_def
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  apply (fastforce simp: ntfn_bound_refs_def obj_at_def ntfn_q_refs_no_TCBBound
                  elim!: pred_tcb_weakenE
                  dest!: bound_tcb_bound_notification_at refs_in_ntfn_bound_refs symreftype_inverse'
                  split: option.splits)
  done

crunch cancel_all_signals
  for bound_tcb_at[wp]: "bound_tcb_at P t"
  (wp: mapM_x_wp_inv)


lemma waiting_ntfn_list_tcb_at:
  "\<lbrakk>valid_objs s; ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = WaitingNtfn x\<rbrakk> \<Longrightarrow> \<forall>t \<in> set x. tcb_at t s"
  by (fastforce elim!: obj_at_valid_objsE simp:valid_obj_def valid_ntfn_def)

lemma tcb_at_ko_at:
  "tcb_at p s \<Longrightarrow> \<exists>tcb. ko_at (TCB tcb) p s"
  by (fastforce simp: obj_at_def is_tcb)

lemma tcb_state_refs_no_tcb:
  "\<lbrakk>valid_objs s; tcb_at y s; (x, ref) \<in> state_refs_of s y\<rbrakk> \<Longrightarrow> ~ tcb_at x s"
  apply (clarsimp simp: ko_at_state_refs_ofD dest!: tcb_at_ko_at)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: is_tcb valid_obj_def)
  apply (erule disjE)
   apply (clarsimp simp: tcb_st_refs_of_def valid_tcb_def valid_tcb_state_def obj_at_def is_ep is_ntfn
                  split:thread_state.splits)
  apply (clarsimp simp: tcb_bound_refs_def valid_tcb_def obj_at_def is_ntfn
                  split:option.splits)
  done

lemma cancel_all_signals_invs:
  "\<lbrace>invs\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp cancel_all_invs_helper set_simple_ko_valid_objs valid_irq_node_typ
             hoare_vcg_const_Ball_lift
        | wpc
        | simp add: live_def)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (rule conjI)
   apply (fastforce simp: valid_obj_def valid_ntfn_def elim!: obj_at_valid_objsE)
  apply (rule conjI)
   apply (fastforce simp: live_def elim!: if_live_then_nonz_capD)
  apply (rule conjI)
   apply (fastforce simp: is_ntfn elim!: ko_at_weakenE)
  apply (rule conjI)
  apply (fastforce simp: st_tcb_at_refs_of_rev
                    dest: bspec sym_refs_ko_atD
                    elim: st_tcb_ex_cap)
  apply (rule conjI[rotated])
   apply (fastforce elim!: ntfn_queued_st_tcb_at)

  apply (rule delta_sym_refs, assumption)
   apply (fastforce dest!: refs_in_ntfn_bound_refs ko_at_state_refs_ofD
                    split: if_split_asm)
  apply (clarsimp split:if_split_asm)
    apply (fastforce dest: waiting_ntfn_list_tcb_at refs_in_ntfn_bound_refs
                     simp: obj_at_def is_tcb_def)
   apply (rule conjI)
    apply (fastforce dest: refs_in_ntfn_bound_refs symreftype_inverse')
   apply (frule (2) waiting_ntfn_list_tcb_at)
   apply (fastforce simp: st_tcb_at_refs_of_rev refs_in_tcb_bound_refs
                    dest: bspec sym_refs_ko_atD st_tcb_at_state_refs_ofD)
  apply (fastforce simp: ntfn_bound_refs_def valid_obj_def valid_ntfn_def refs_of_rev
                  dest!: symreftype_inverse' ko_at_state_refs_ofD
                  split: option.splits
                  elim!: obj_at_valid_objsE)
  done

lemma cancel_all_unlive_helper:
  "\<lbrace>obj_at (\<lambda>obj. \<not> live obj \<and> (\<forall>tcb. obj \<noteq> TCB tcb)) ptr\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    tcb_sched_action tcb_sched_enqueue t od) q
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule hoare_strengthen_post [OF mapM_x_wp'])
   apply (simp add: set_thread_state_def set_object_def get_object_def)
   apply (wp | simp only: obj_at_exst_update)+
   apply (clarsimp dest!: get_tcb_SomeD)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp elim!: obj_at_weakenE)
  done

crunch possible_switch_to
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

lemma cancel_all_ipc_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> cancel_all_ipc ptr \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: set_simple_ko_def get_ep_queue_def)
    apply wp
    apply (clarsimp simp: live_def elim!: obj_at_weakenE)
   apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
   apply (clarsimp simp: live_def)
  apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
  apply (clarsimp simp: live_def)
  done


(* This lemma should be sufficient provided that each notification object is unbound BEFORE the 'cancel_all_signals' function is invoked. TODO: Check the abstract specification and the C and Haskell implementations that this is indeed the case. *)
lemma cancel_all_signals_unlive[wp]:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None) ntfnptr s\<rbrace>
     cancel_all_signals ntfnptr
   \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ntfnptr\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp
        | wpc
        | simp add: unbind_maybe_notification_def)+
     apply (rule_tac Q'="\<lambda>_. obj_at (is_ntfn and Not \<circ> live) ntfnptr" in hoare_post_imp)
      apply (fastforce elim: obj_at_weakenE)
     apply (wp mapM_x_wp' sts_obj_at_impossible
          | simp add: is_ntfn)+
    apply (simp add: set_simple_ko_def)
    apply (wp get_object_wp obj_set_prop_at)
  apply (auto simp: live_def pred_tcb_at_def obj_at_def)
  done


crunch cancel_all_ipc
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)

crunch cancel_all_signals
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp thread_set_cte_wp_at_trivial
   simp: tcb_cap_cases_def)

lemma cancel_badged_sends_filterM_helper':
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs s  \<and> sym_refs (state_hyp_refs_of s) \<and> distinct (xs @ ys) \<and> ep_at epptr s
           \<and> ex_nonz_cap_to epptr s
           \<and> sym_refs ((state_refs_of s) (epptr := ((set (xs @ ys)) \<times> {EPSend})))
           \<and> (\<forall>x \<in> set (xs @ ys). {r \<in> state_refs_of s x. snd r \<noteq> TCBBound} = {(epptr, TCBBlockedSend)})\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> tcb_sched_action action t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs s \<and> sym_refs (state_hyp_refs_of s)
            \<and> ep_at epptr s \<and> (\<forall>x \<in> set (xs @ ys). tcb_at x s)
            \<and> ex_nonz_cap_to epptr s
            \<and> (\<forall>y \<in> set ys. {r \<in> state_refs_of s y. snd r \<noteq> TCBBound} = {(epptr, TCBBlockedSend)})
            \<and> distinct rv \<and> distinct (xs @ ys) \<and> (set rv \<subseteq> set xs)
            \<and> sym_refs ((state_refs_of s) (epptr := ((set rv \<union> set ys) \<times> {EPSend})))\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply (rule allI, simp)
   apply wp
   apply clarsimp
   apply (drule(1) bspec, drule singleton_eqD, clarsimp, drule state_refs_of_elemD)
   apply (clarsimp simp: st_tcb_at_refs_of_rev pred_tcb_at_def is_tcb
                  elim!: obj_at_weakenE)
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule bind_wp_fwd)
  apply (rule bind_wp [OF _ gts_sp])
  apply (rule hoare_pre,
         wpsimp wp: valid_irq_node_typ sts_only_idle hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: valid_tcb_state_def)
  apply (rule conjI[rotated])
   apply blast
  apply clarsimp
  apply (thin_tac "obj_at f epptr s" for f s)
  apply (thin_tac "tcb_at x s" for x s)
  apply (thin_tac "sym_refs (state_hyp_refs_of s)" for s)
  apply (frule singleton_eqD, clarify, drule state_refs_of_elemD)
  apply (frule(1) if_live_then_nonz_capD)
  apply (rule refs_of_live, clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev)
  apply (clarsimp simp: pred_tcb_def2 valid_idle_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
   apply (drule(1) valid_reply_capsD, clarsimp simp: st_tcb_def2)
  apply (rule conjI, blast)
  apply (rule conjI, blast)
  apply (erule delta_sym_refs)
   apply (auto dest!: get_tcb_ko_atD ko_at_state_refs_ofD symreftype_inverse'
                      refs_in_tcb_bound_refs
               split: if_split_asm)[2]
  done

lemmas cancel_badged_sends_filterM_helper
    = spec [where x=Nil, OF cancel_badged_sends_filterM_helper', simplified]

lemma cancel_badged_sends_invs_helper:
  "{r. snd r \<noteq> TCBBound \<and>
       (r \<in> tcb_st_refs_of ts \<or> r \<in> tcb_bound_refs ntfnptr)} =
   tcb_st_refs_of ts"
  by (auto simp add: tcb_st_refs_of_def tcb_bound_refs_def split: thread_state.splits option.splits)

lemma cancel_badged_sends_invs[wp]:
  "\<lbrace>invs\<rbrace> cancel_badged_sends epptr badge \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep; simp)
    apply wpsimp
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wpsimp wp: valid_irq_node_typ)
     apply (simp add: fun_upd_def[symmetric] ep_redux_simps ep_at_def2[symmetric, simplified]
                cong: list.case_cong)
     apply (rule hoare_strengthen_post,
            rule cancel_badged_sends_filterM_helper[where epptr=epptr])
     apply (auto intro:obj_at_weakenE)[1]
    apply (wpsimp wp: valid_irq_node_typ set_endpoint_ep_at)
   apply (clarsimp simp: valid_ep_def conj_comms)
   apply (subst obj_at_weakenE, simp, fastforce)
    apply (clarsimp simp: is_ep_def)
   apply (frule(1) sym_refs_ko_atD, clarsimp)
   apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
   apply (erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_refs_of_rev)
   apply (simp add: fun_upd_idem obj_at_def is_ep_def | subst fun_upd_def[symmetric])+
   apply (clarsimp, drule(1) bspec)
   apply (drule st_tcb_at_state_refs_ofD)
   apply (clarsimp simp only: cancel_badged_sends_invs_helper Un_iff, clarsimp)
   apply (simp add: set_eq_subset)
  apply wpsimp
  done

(* FIXME rule_format? *)
lemma real_cte_emptyable_strg:
  "real_cte_at p s \<longrightarrow> emptyable p s"
  by (clarsimp simp: emptyable_def obj_at_def is_tcb is_cap_table)

end
