(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IpcCancel_AI
imports Schedule_AI
begin

lemma blocked_ipc_cancel_simple:
  "\<lbrace>tcb_at t\<rbrace> blocked_ipc_cancel ts t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: blocked_ipc_cancel_def | wp sts_st_tcb_at')+


lemma async_ipc_cancel_simple:
  "\<lbrace>\<top>\<rbrace> async_ipc_cancel t aep \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: async_ipc_cancel_def | wp sts_st_tcb_at')+


crunch  typ_at: ep_cancel_all "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)


lemma cancel_all_helper:
  " \<lbrace>valid_objs and
    (\<lambda>s. \<forall>t \<in> set queue. st_tcb_at (\<lambda>st. \<not> halted st) t s) \<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) queue
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [where S="set queue", simplified])
    apply (wp, simp, wp hoare_vcg_const_Ball_lift sts_st_tcb_at_cases, simp)
    apply (clarsimp elim: st_tcb_weakenE)
    apply (erule(1) my_BallE)
    apply (clarsimp simp: st_tcb_def2)
    apply (frule(1) valid_tcb_objs)
    apply (clarsimp simp: valid_tcb_def valid_tcb_state_def
                          cte_wp_at_cases tcb_cap_cases_def
                   dest!: get_tcb_SomeD)
   apply simp+
  done


lemma ep_cancel_all_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   ep_cancel_all ptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: ep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, simp)
   apply (wp cancel_all_helper hoare_vcg_const_Ball_lift
        | clarsimp simp: ep_queued_st_tcb_at obj_at_def
                         valid_ep_def)+
  done


crunch typ_at: aep_cancel_all "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)


lemma aep_cancel_all_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   aep_cancel_all ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: aep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac aep, simp_all)
    apply (wp, simp)
   apply (wp cancel_all_helper hoare_vcg_const_Ball_lift
             set_aep_valid_objs
        | clarsimp simp: aep_queued_st_tcb_at obj_at_def
                         valid_aep_def)+
  done


lemma get_ep_queue_inv[wp]:
  "\<lbrace>P\<rbrace> get_ep_queue ep \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases ep, simp_all add: get_ep_queue_def)


lemma ep_cancel_all_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> ep_cancel_all epptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding ep_cancel_all_def
  by (wp ep_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases | simp)+


lemmas ep_cancel_all_makes_simple[wp] =
  ep_cancel_all_st_tcb_at[where P=simple, simplified]


lemma aep_cancel_all_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> aep_cancel_all aepptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding aep_cancel_all_def
  by (wp aep_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases
         | simp)+


lemmas aep_cancel_all_makes_simple[wp] =
       aep_cancel_all_st_tcb_at[where P=simple, simplified]

lemma get_blocking_ipc_endpoint_inv[wp]:
  "\<lbrace>P\<rbrace> get_blocking_ipc_endpoint st \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases st, simp_all add: get_blocking_ipc_endpoint_def)


lemma blocked_ipc_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> P Structures_A.Inactive)\<rbrace>
     blocked_ipc_cancel st t
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: blocked_ipc_cancel_def)
  apply (wp sts_st_tcb_at_cases static_imp_wp, simp+)
  done


lemma async_ipc_cancel_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> (P Structures_A.Running \<and> P Structures_A.Inactive))\<rbrace>
     async_ipc_cancel t aep
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: async_ipc_cancel_def)
  apply (wp sts_st_tcb_at_cases aep_cases_weak_wp static_imp_wp)
  apply simp
  done

lemma fast_finalise_misc[wp]:
"\<lbrace>st_tcb_at simple t \<rbrace> fast_finalise  a b
\<lbrace>\<lambda>_. st_tcb_at simple t\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp|clarsimp)+
  done
 

crunch st_tcb_at_simple[wp]: reply_ipc_cancel "st_tcb_at simple t"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state
   simp: crunch_simps unless_def fast_finalise.simps)

lemma ipc_cancel_simple [wp]:
  "\<lbrace>\<top>\<rbrace> ipc_cancel t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
         apply (wp hoare_strengthen_post [OF blocked_ipc_cancel_simple]
                   hoare_strengthen_post [OF async_ipc_cancel_simple]
                   hoare_strengthen_post
                      [OF reply_ipc_cancel_st_tcb_at_simple [where t=t]]
                   sts_st_tcb_at_cases
                   hoare_drop_imps
                 | clarsimp elim!: st_tcb_weakenE st_tcb_at_tcb_at)+
  done


lemma blocked_ipc_cancel_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> blocked_ipc_cancel st t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: blocked_ipc_cancel_def get_blocking_ipc_endpoint_def get_ep_queue_def)
  apply wp
    apply (case_tac ep, simp_all)[1]
     apply wp
  apply (cases st, simp_all)
  done


lemma blocked_ipc_cancel_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> blocked_ipc_cancel st t' \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp


lemma fast_finalise_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> fast_finalise a b \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp ep_cancel_all_typ_at aep_cancel_all_typ_at|clarsimp)+
  done


crunch typ_at[wp]: reply_ipc_cancel "\<lambda>s. P (typ_at T p s)" 
  (wp: crunch_wps hoare_vcg_split_ifE select_wp
     simp: crunch_simps unless_def)


crunch typ_at[wp]: ipc_cancel "\<lambda>s. P (typ_at T p s)" 


lemma ipc_cancel_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> ipc_cancel t' \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp


lemma gbep_ret:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr x \<or> 
     st = Structures_A.BlockedOnSend epPtr p \<rbrakk> \<Longrightarrow>
  get_blocking_ipc_endpoint st = return epPtr"
  by (auto simp add: get_blocking_ipc_endpoint_def)


lemma st_tcb_at_valid_st2: 
  "\<lbrakk> st_tcb_at (op = st) t s; valid_objs s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def get_tcb_def st_tcb_at_def 
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done


definition
 "emptyable \<equiv> \<lambda>p s. (tcb_at (fst p) s \<and> snd p = tcb_cnode_index 2) \<longrightarrow>
                          st_tcb_at halted (fst p) s"


locale delete_one_abs =
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs and emptyable p\<rbrace> (cap_delete_one p :: (unit,'a::state_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"

  assumes delete_one_deletes:
    "\<lbrace>\<top>\<rbrace> (cap_delete_one sl :: (unit,'a::state_ext) s_monad) \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"

  assumes delete_one_caps_of_state:
    "\<And>P p. \<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
                  \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
             (cap_delete_one p :: (unit,'a::state_ext) s_monad)
            \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>" 


lemma reply_master_no_descendants_no_reply:
  "\<lbrakk> valid_mdb s; valid_reply_masters s; tcb_at t s \<rbrakk> \<Longrightarrow>
   descendants_of (t, tcb_cnode_index 2) (cdt s) = {} \<longrightarrow> \<not> has_reply_cap t s"
  by (fastforce simp: invs_def valid_state_def valid_mdb_def has_reply_cap_def
                     cte_wp_at_caps_of_state reply_mdb_def
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
  apply (clarsimp simp: tcb_cap_wp_at tcb_at_st_tcb_at invs_valid_objs
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
     get_blocking_ipc_endpoint st
   \<lbrace>\<lambda>ep. P and K ((\<exists>d. st = Structures_A.BlockedOnReceive ep d)
                    \<or> (\<exists>d. st = Structures_A.BlockedOnSend ep d))\<rbrace>"
  apply (cases st, simp_all add: get_blocking_ipc_endpoint_def)
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


crunch v_ker_map[wp]: set_endpoint "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

crunch eq_ker_map[wp]: set_endpoint "equal_kernel_mappings"
  (ignore: set_object wp: set_object_equal_mappings crunch_wps)


lemma set_endpoint_global_pd_mappings[wp]:
  "\<lbrace>valid_global_pd_mappings\<rbrace>
      set_endpoint p val
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp get_object_wp set_object_global_pd_mappings)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.splits)
  done  

lemma set_ep_cap_refs_in_kernel_window [wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_endpoint ep p \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  unfolding set_endpoint_def
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def same_caps_more_simps is_ep_def 
                  split: Structures_A.kernel_object.splits)
  done

lemma set_endpoint_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp set_object_valid_ioc_no_caps)
  apply (clarsimp simp add: valid_def get_object_def simpler_gets_def split_def
             bind_def assert_def return_def fail_def obj_at_def is_tcb
             is_cap_table a_type_simps
           split: Structures_A.kernel_object.splits)
  done

lemma set_endpoint_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_endpoint p q \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  apply (simp add: valid_machine_state_def in_user_frame_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_ex_lift)
  apply (simp add: set_endpoint_def)
  apply (wp hoare_drop_imps)
  done

lemma blocked_ipc_cancel_invs:
  "\<lbrace>invs and st_tcb_at (op = st) t\<rbrace> blocked_ipc_cancel st t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: blocked_ipc_cancel_def)
  apply (rule hoare_seq_ext [OF _ gbi_ep_sp])
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (rule hoare_seq_ext [OF _ get_epq_sp])
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle)
   apply (simp add: valid_tcb_state_def)
   apply (strengthen reply_cap_doesnt_exist_strg)
   apply simp
   apply (wp valid_irq_node_typ)
  apply (subgoal_tac "ep \<noteq> Structures_A.IdleEP")
   apply (clarsimp simp: ep_redux_simps2 cong: if_cong)
   apply (frule(1) if_live_then_nonz_capD, clarsimp+)
   apply (frule ko_at_state_refs_ofD)
   apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def)
   apply (frule st_tcb_at_state_refs_ofD)
   apply (subgoal_tac "epptr \<notin> set (remove1 t queue)")
    apply (case_tac ep, simp_all add: valid_ep_def)[1]
     apply (rule conjI, erule delta_sym_refs)
       apply (clarsimp split: split_if_asm)+
      apply auto[1]
     apply (clarsimp simp add: obj_at_def is_ep idle_not_queued)
     apply (fastforce dest: idle_no_refs elim: st_tcb_weakenE)
    apply (rule conjI, erule delta_sym_refs)
      apply (clarsimp simp: split_if_asm)+
     apply auto[1]
    apply (simp add: obj_at_def is_ep idle_not_queued)
    apply (fastforce dest: idle_no_refs elim: st_tcb_weakenE)
   apply (case_tac ep, simp_all add: valid_ep_def)[1]
    apply (clarsimp, drule(1) bspec, clarsimp simp: obj_at_def is_tcb_def)+
  apply fastforce
  done

lemma async_ipc_cancel_invs:
  "\<lbrace>invs and st_tcb_at (op = (Structures_A.BlockedOnAsyncEvent aep)) t\<rbrace> 
  async_ipc_cancel t aep 
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: async_ipc_cancel_def
                   invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac aepa, simp_all)[1]
  apply (rule hoare_pre)
   apply (wp set_aep_valid_objs valid_irq_node_typ sts_only_idle
           | simp add: valid_tcb_state_def
           | strengthen reply_cap_doesnt_exist_strg)+
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong if_cong)
  apply (frule(1) if_live_then_nonz_capD, clarsimp+)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def valid_aep_def)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: split_if_asm)+
  apply (simp add: obj_at_def is_aep idle_not_queued)
  apply (fastforce dest: idle_no_refs elim: st_tcb_weakenE)
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
  apply (clarsimp simp: tcb_cap_wp_at tcb_at_st_tcb_at invs_valid_objs
                        tcb_cap_cases_def)
  done

lemma reply_ipc_cancel_invs:
  assumes delete: "\<And>p. \<lbrace>invs and emptyable p\<rbrace>
                        (cap_delete_one p :: (unit,'z::state_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  shows           "\<lbrace>invs\<rbrace> (reply_ipc_cancel t :: (unit,'z::state_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_ipc_cancel_def)
  apply (wp delete select_wp)
  apply (rule_tac Q="\<lambda>rv. invs" in hoare_post_imp)
   apply (fastforce simp: emptyable_def dest: reply_slot_not_descendant)
  apply (wp thread_set_invs_trivial)
   apply (clarsimp simp: tcb_cap_cases_def)+
  done

lemma (in delete_one_abs) ipc_cancel_invs[wp]:
  "\<lbrace>invs\<rbrace> (ipc_cancel t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
        apply (auto intro!: hoare_weaken_pre [OF return_wp]
                            hoare_weaken_pre [OF blocked_ipc_cancel_invs]
                            hoare_weaken_pre [OF async_ipc_cancel_invs]
                            hoare_weaken_pre [OF reply_ipc_cancel_invs]
                            delete_one_invs
                     elim!: st_tcb_weakenE)
  done

lemma ipc_cancel_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> ipc_cancel p \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma ipc_cancel_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> ipc_cancel t \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  by (wp valid_cte_at_typ)


lemma stronger_get_ep_inv:
  "\<lbrace>\<lambda>s. ep_at epptr s \<longrightarrow> P s\<rbrace> get_endpoint epptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: get_endpoint_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply (case_tac kobj, simp_all)
  apply wp
  apply (clarsimp simp add: obj_at_def is_ep_def)
  done


lemma stronger_get_aep_inv:
  "\<lbrace>\<lambda>s. aep_at epptr s \<longrightarrow> P s\<rbrace> get_async_ep epptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: get_async_ep_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply (case_tac kobj, simp_all)
  apply wp
  apply (clarsimp simp: is_aep_def obj_at_def)
  done


lemma valid_ep_get_ep2:
  "\<lbrace>valid_objs\<rbrace> get_endpoint epptr \<lbrace>valid_ep\<rbrace>"
  apply (simp add: get_endpoint_def)
  apply (rule hoare_seq_ext [OF _ get_object_valid])
  apply (case_tac kobj, simp_all)
  apply wp
  apply (simp add: valid_obj_def)
  done


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


lemma blocked_ipc_cancel_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> blocked_ipc_cancel st t \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: blocked_ipc_cancel_def)
  apply (wp stronger_get_ep_inv valid_ep_get_ep2 valid_ep_queue_subset
         | simp only: valid_inactive simp_thms
                cong: imp_cong
         | rule hoare_drop_imps
         | clarsimp)+
  done


lemma async_ipc_cancel_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> async_ipc_cancel t aepptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: async_ipc_cancel_def)
  apply (wp set_aep_valid_objs | simp only: valid_inactive | simp)+
   prefer 2
   apply (rule get_aep_sp)
  apply (case_tac aep, simp_all)
  apply wp
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_aep_def)
  done


lemma tcb_in_valid_state:
  "\<lbrakk> st_tcb_at P t s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>st. P st \<and> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def st_tcb_at_def obj_at_def)
  apply (erule my_BallE, erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  apply blast
  done


lemma no_refs_simple_strg:
  "st_tcb_at simple t s \<and> P {} \<longrightarrow> st_tcb_at (\<lambda>st. P (tcb_st_refs_of st)) t s"
  by (fastforce elim!: st_tcb_weakenE)+

crunch it[wp]: ep_cancel_all "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp simp: unless_def crunch_simps)

crunch it[wp]: aep_cancel_all "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp simp: unless_def crunch_simps)

lemma fast_finalise_it:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> fast_finalise a final \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp|clarsimp)+
  done

crunch it[wp]: reply_ipc_cancel  "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp simp: unless_def crunch_simps)

crunch it[wp]: ipc_cancel "\<lambda>s. P (idle_thread s)"

lemma reply_cap_descends_from_master:
  "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow>
   \<forall>sl\<in>descendants_of (t, tcb_cnode_index 2) (cdt s).  \<forall>sl'. sl' \<noteq> sl \<longrightarrow>
      caps_of_state s sl' \<noteq> Some (cap.ReplyCap t False)"
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
  apply (clarsimp simp: tcb_cap_wp_at tcb_at_st_tcb_at invs_valid_objs
                        tcb_cap_cases_def is_cap_simps)
  done

lemma (in delete_one_abs) reply_ipc_cancel_no_reply_cap[wp]:
  "\<lbrace>invs and tcb_at t\<rbrace> (reply_ipc_cancel t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: reply_ipc_cancel_def)
  apply wp
     apply (rule_tac Q="\<lambda>rvp s. cte_wp_at (\<lambda>c. c = cap.NullCap) x s \<and>
                                (\<forall>sl. sl \<noteq> x \<longrightarrow>
                                  caps_of_state s sl \<noteq> Some (cap.ReplyCap t False))"
                  in hoare_strengthen_post)
      apply (wp hoare_vcg_conj_lift hoare_vcg_all_lift
                delete_one_deletes delete_one_caps_of_state)
     apply (clarsimp simp: has_reply_cap_def cte_wp_at_caps_of_state)
     apply (case_tac "(aa, ba) = (a, b)", simp_all)[1]
    apply (wp hoare_vcg_all_lift select_wp | simp del: split_paired_All)+
  apply (rule_tac Q="\<lambda>_ s. invs s \<and> tcb_at t s" in hoare_post_imp)
   apply (erule conjE)
   apply (frule(1) reply_cap_descends_from_master)
   apply (auto dest: reply_master_no_descendants_no_reply[rotated -1])
  apply (wp thread_set_invs_trivial | clarsimp simp: tcb_cap_cases_def)+
  done

lemma (in delete_one_abs) ipc_cancel_no_reply_cap[wp]:
  "\<lbrace>invs and tcb_at t\<rbrace> (ipc_cancel t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (wp | wpc)+
        apply (strengthen reply_cap_doesnt_exist_strg
             | wp hoare_post_imp [OF invs_valid_reply_caps]
                  reply_ipc_cancel_no_reply_cap
                  async_ipc_cancel_invs async_ipc_cancel_st_tcb_at_general
                  blocked_ipc_cancel_invs blocked_ipc_st_tcb_at_general
             | simp add: o_def)+
  apply (rule_tac Q="\<lambda>rv. st_tcb_at (op = rv) t and invs" in hoare_strengthen_post)
   apply (wp gts_st_tcb | simp)+
  apply (fastforce simp: invs_def valid_state_def st_tcb_at_tcb_at
                 elim!: st_tcb_weakenE)+
  done

lemma (in delete_one_abs) suspend_invs[wp]:
  "\<lbrace>invs and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   (suspend t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp sts_invs_minor ipc_cancel_invs ipc_cancel_no_reply_cap
       | strengthen no_refs_simple_strg | simp)+
  done

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (simp add: suspend_def | wp)+


lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp


declare if_cong [cong del]


crunch cte_wp_at[wp]: blocked_ipc_cancel "cte_wp_at P p"
  (wp: crunch_wps)

crunch cte_wp_at[wp]: async_ipc_cancel "cte_wp_at P p"
  (wp: crunch_wps)


locale delete_one_pre =
  assumes delete_one_cte_wp_at_preserved:
    "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
     \<lbrace>cte_wp_at P sl\<rbrace> (cap_delete_one sl' :: (unit,'a::state_ext) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"


lemma (in delete_one_pre) reply_ipc_cancel_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (reply_ipc_cancel t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: reply_ipc_cancel_def)
  apply (wp select_wp delete_one_cte_wp_at_preserved | simp)+
  apply (rule_tac Q="\<lambda>_. cte_wp_at P p" in hoare_post_imp, clarsimp)
  apply (wp thread_set_cte_wp_at_trivial, clarsimp simp: tcb_cap_cases_def)
  done


lemma (in delete_one_pre) ipc_cancel_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (ipc_cancel t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (rule hoare_pre)
   apply (wp reply_ipc_cancel_cte_wp_at_preserved | wpcw | simp)+
  done


lemma (in delete_one_pre) suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,'a) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def, wp, simp, wp ipc_cancel_cte_wp_at_preserved)

(* FIXME - move *)
lemma obj_at_exst_update:
  "obj_at P p (trans_state f s) = obj_at P p s"
  by (simp add: obj_at_def)

lemma suspend_unlive:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) t\<rbrace>"
  apply (simp add: suspend_def set_thread_state_def set_object_def)
  apply (wp | simp only: obj_at_exst_update)+
  apply (simp add: obj_at_def)
  apply wp
  done

lemma cancel_all_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then {} else state_refs_of s x)
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s))\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply wp
   apply simp
   apply wp[1]
  apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle)
   apply (rule sts_st_tcb_at_cases, simp)
  apply (strengthen reply_cap_doesnt_exist_strg)
  apply (auto simp: valid_tcb_state_def idle_no_ex_cap o_def
             elim!: rsubst[where P=sym_refs] st_tcb_weakenE
            intro!: ext)
  done

lemma ep_cancel_all_invs_helper:
  assumes x: "\<And>x ko. (x, symreftype k) \<in> refs_of ko
                      \<Longrightarrow> refs_of ko = {(x, symreftype k)}"
  shows
  "\<lbrace>invs and obj_at (\<lambda>ko. is_ep ko \<and> refs_of ko = set q \<times> {k}) p\<rbrace>
     do y \<leftarrow> set_endpoint p Structures_A.endpoint.IdleEP;
        y \<leftarrow> mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                           do_extended_op (tcb_sched_action (tcb_sched_enqueue) t) od) q;
        do_extended_op reschedule_required
    od \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (subst bind_assoc[symmetric])
  apply (rule hoare_seq_ext)
   apply wp
   apply simp
  apply (rule hoare_pre, wp cancel_all_invs_helper hoare_vcg_const_Ball_lift
                            valid_irq_node_typ)
  apply (clarsimp simp: valid_ep_def invs_def valid_state_def valid_pspace_def)
  apply (rule conjI)
   apply (clarsimp elim!: obj_at_weakenE)
  apply (rule conjI)
   apply clarsimp
   apply (drule(1) sym_refs_obj_atD, clarsimp)
   apply (drule(1) bspec, erule(1) if_live_then_nonz_capD)
   apply (rule refs_of_live, clarsimp)
  apply (rule conjI)
   apply (frule(1) sym_refs_obj_atD)
   apply (clarsimp dest!: obj_at_state_refs_ofD)
   apply (erule delta_sym_refs)
    apply (clarsimp split: split_if_asm)+
   apply (drule(1) bspec)
   apply (clarsimp dest!: obj_at_state_refs_ofD x)
  apply (subgoal_tac "\<exists>ep. ko_at (Endpoint ep) p s", clarsimp)
   apply (subgoal_tac "\<exists>rt. (x, rt) \<in> ep_q_refs_of ep", clarsimp)
    apply (fastforce elim!: ep_queued_st_tcb_at)
   apply (clarsimp simp: obj_at_def is_ep)+ 
  done

lemma ep_cancel_all_invs:
  "\<lbrace>invs\<rbrace> ep_cancel_all epptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: ep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, fastforce)
   apply (rule hoare_pre, rule ep_cancel_all_invs_helper[where k=EPSend])
    apply (clarsimp simp: refs_of_rev)
   apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  apply (rule hoare_pre, rule ep_cancel_all_invs_helper[where k=EPRecv])
   apply (clarsimp simp: refs_of_rev)
  apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  done

lemma aep_cancel_all_invs:
  "\<lbrace>invs\<rbrace> aep_cancel_all aepptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: aep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac aep, simp_all)
    apply (wp, fastforce)
   apply (wp, simp, wp cancel_all_invs_helper)
   apply (rule hoare_pre, wp set_aep_valid_objs hoare_vcg_const_Ball_lift
                             valid_irq_node_typ)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_aep_def)
   apply (rule conjI, erule ko_at_weakenE)
    apply (simp add: is_aep)
   apply (frule ko_at_state_refs_ofD)
   apply (frule(1) sym_refs_ko_atD)
   apply (clarsimp simp: st_tcb_at_refs_of_rev)
   apply (rule conjI, clarsimp)
    apply (drule(1) bspec, erule(1) st_tcb_ex_cap, clarsimp)
   apply (rule conjI[rotated])
    apply (fastforce elim!: aep_queued_st_tcb_at)
   apply (erule delta_sym_refs)
    apply (clarsimp split: split_if_asm)+
   apply (drule(1) bspec, clarsimp dest!: st_tcb_at_state_refs_ofD)
  apply (wp, fastforce)
  done

lemma cancel_all_unlive_helper:
  "\<lbrace>obj_at (\<lambda>obj. \<not> live obj \<and> (\<forall>tcb. obj \<noteq> TCB tcb)) ptr\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule hoare_strengthen_post [OF mapM_x_wp'])
   apply (simp add: set_thread_state_def set_object_def)
   apply (wp | simp only: obj_at_exst_update)+
   apply (clarsimp dest!: get_tcb_SomeD)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp elim!: obj_at_weakenE)
  done


lemma ep_cancel_all_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> ep_cancel_all ptr \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (simp add: ep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (case_tac ep, simp_all add: set_endpoint_def get_ep_queue_def)
    apply wp
    apply (clarsimp elim!: obj_at_weakenE)
   apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
   apply clarsimp
  apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
  apply clarsimp
  done


lemma aep_cancel_all_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> aep_cancel_all ptr \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (simp add: aep_cancel_all_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (case_tac aep, simp_all add: set_async_ep_def)
    apply wp
    apply (clarsimp elim!: obj_at_weakenE)
   apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
   apply clarsimp
  apply wp
  apply (clarsimp elim!: obj_at_weakenE)
  done


crunch cte_wp_at[wp]: ep_cancel_all "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)


crunch cte_wp_at[wp]: aep_cancel_all "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)

lemma ep_cancel_badged_sends_filterM_helper':
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs s \<and> distinct (xs @ ys) \<and> ep_at epptr s
           \<and> ex_nonz_cap_to epptr s
           \<and> sym_refs ((state_refs_of s) (epptr := ((set (xs @ ys)) \<times> {EPSend})))
           \<and> (\<forall>x \<in> set (xs @ ys). state_refs_of s x = {(epptr, TCBBlockedSend)})\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> do_extended_op (tcb_sched_action action t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs s
            \<and> ep_at epptr s \<and> (\<forall>x \<in> set (xs @ ys). tcb_at x s)
            \<and> ex_nonz_cap_to epptr s
            \<and> (\<forall>y \<in> set ys. state_refs_of s y = {(epptr, TCBBlockedSend)})
            \<and> distinct rv \<and> distinct (xs @ ys) \<and> (set rv \<subseteq> set xs)
            \<and> sym_refs ((state_refs_of s) (epptr := ((set rv \<union> set ys) \<times> {EPSend})))\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply (rule allI, simp)
   apply wp
   apply clarsimp
   apply (drule(1) bspec, drule singleton_eqD, drule state_refs_of_elemD)
   apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_def is_tcb
                  elim!: obj_at_weakenE)
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle hoare_vcg_const_Ball_lift | simp)+
  apply (clarsimp simp: valid_tcb_state_def)
  apply (rule conjI[rotated])
   apply blast
  apply clarsimp
  apply (thin_tac "ep_at epptr s" for s)
  apply (thin_tac "tcb_at x s" for x s)
  apply (frule singleton_eqD, drule state_refs_of_elemD)
  apply (frule(1) if_live_then_nonz_capD, rule refs_of_live, clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev)
  apply (clarsimp simp: st_tcb_def2 valid_idle_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
   apply (drule(1) valid_reply_capsD, clarsimp simp: st_tcb_def2)
  apply (rule conjI, blast)
  apply (rule conjI, blast)
  apply (erule delta_sym_refs)
   apply (auto split: split_if_asm)
  done

lemmas ep_cancel_badged_sends_filterM_helper
    = spec [where x=Nil, OF ep_cancel_badged_sends_filterM_helper', simplified]

lemma ep_cancel_badged_sends_invs[wp]:
  "\<lbrace>invs\<rbrace> ep_cancel_badged_sends epptr badge \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: ep_cancel_badged_sends_def)
  apply (rule hoare_seq_ext [OF _ get_endpoint_sp])
  apply (case_tac ep, simp_all)
    apply (wp, simp)
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wp, simp, wp valid_irq_node_typ)
     apply (simp add: fun_upd_def[symmetric] ep_redux_simps
                cong: list.case_cong)
     apply (rule hoare_strengthen_post,
            rule ep_cancel_badged_sends_filterM_helper[where epptr=epptr])
     apply clarsimp
     apply blast
    apply (wp valid_irq_node_typ)
   apply (clarsimp simp: valid_ep_def conj_comms)
   apply (subst obj_at_weakenE[where P'=is_ep], assumption)
    apply (clarsimp simp: is_ep_def)
   apply (frule(1) sym_refs_ko_atD, clarsimp)
   apply (frule(1) if_live_then_nonz_capD, clarsimp+)
   apply (erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_refs_of_rev)
   apply (simp add: fun_upd_idem | subst fun_upd_def[symmetric])+
   apply (clarsimp, drule(1) bspec)
   apply (drule st_tcb_at_state_refs_ofD, clarsimp)
   apply (simp add: set_eq_subset)
  apply (wp | simp)+
  done

lemma real_cte_emptyable_strg:
  "real_cte_at p s \<longrightarrow> emptyable p s"
  by (clarsimp simp: emptyable_def obj_at_def is_tcb is_cap_table)


end
