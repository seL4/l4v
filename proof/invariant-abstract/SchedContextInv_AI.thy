(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory SchedContextInv_AI
imports "./$L4V_ARCH/ArchIpc_AI"
begin

text {* invocation related lemmas *}

primrec
  valid_sched_context_inv :: "sched_context_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_context_inv (InvokeSchedContextConsumed scptr args)
     = (sc_at scptr and ex_nonz_cap_to scptr)"
  | "valid_sched_context_inv (InvokeSchedContextBind scptr cap)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow> bound_sc_tcb_at (op = None) t
                                      and ex_nonz_cap_to t and sc_tcb_sc_at (op = None) scptr
             | NotificationCap n _ _ \<Rightarrow>
                   obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_sc ntfn = None) n
                   and ex_nonz_cap_to n  and sc_ntfn_sc_at (op = None) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbindObject scptr cap)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow>
                   ex_nonz_cap_to t and sc_tcb_sc_at (\<lambda>tcb. tcb = (Some t)) scptr
             | NotificationCap n _ _ \<Rightarrow>
                   ex_nonz_cap_to n and sc_ntfn_sc_at (\<lambda>ntfn. ntfn = (Some n)) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbind scptr)
     = (sc_at scptr and ex_nonz_cap_to scptr)"
  | "valid_sched_context_inv (InvokeSchedContextYieldTo scptr args)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr(* and (\<lambda>s. st_tcb_at (op = Restart) (cur_thread s) s)*)
          and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s)
          and sc_yf_sc_at (op = None) scptr and (\<lambda>s. bound_yt_tcb_at (op = None) (cur_thread s) s)
          and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb.\<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                 (*  \<and> (mcpriority_tcb_at (\<lambda>mcp. (tcb_priority (the (get_etcb t s))) \<le> mcp)
                                                                      (cur_thread s) s)*)) scptr s))"

primrec
  valid_sched_control_inv :: "sched_control_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)
     = (sc_at scptr and ex_nonz_cap_to scptr
        (* probably also need something like \<and> mrefills \<le> max_extra_refills *))"


lemma sched_context_bind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_bind_tcb sc tcb \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_bind_tcb_def)

lemma sched_context_yield_to_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_yield_to sc_ptr args \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_yield_to_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma invoke_sched_context_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_context i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i;
      wpsimp wp: dxo_wp_weak mapM_x_wp get_sched_context_wp
       simp: invoke_sched_context_def sched_context_bind_ntfn_def)

crunch typ_at[wp]: charge_budget "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

lemma check_budget_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> check_budget \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: check_budget_def split_del: if_split
            wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunch typ_at[wp]: commit_time "\<lambda>s::det_ext state. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

crunch typ_at[wp]: tcb_release_remove "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

lemma invoke_sched_control_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_control_configure i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i; wpsimp simp: invoke_sched_control_configure_def split_del: if_splits
                  wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma invoke_sched_context_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_context_typ_at [where P=id, simplified])

lemma invoke_sched_control_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_control_typ_at [where P=id, simplified])

lemma invoke_sched_context_invs[wp]:
  "\<lbrace>invs and valid_sched_context_inv i\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i;
      wpsimp simp: invoke_sched_context_def set_consumed_def valid_sched_context_inv_def)
   apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def sc_ntfn_sc_at_def is_sc_obj_def is_tcb
      valid_cap_def idle_no_ex_cap split: cap.split_asm)+
   apply (frule invs_valid_global_refs)
   apply (frule invs_valid_objs, clarsimp simp: idle_no_ex_cap)
  apply (frule invs_valid_global_refs)
  apply (frule invs_valid_objs, clarsimp simp: idle_no_ex_cap)
  done

lemma update_sc_badge_invs:
  "\<lbrace>invs and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
      update_sched_context p (sc\<lparr>sc_badge := i \<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                simp_del: fun_upd_apply)
  apply safe
    apply (fastforce simp: valid_objs_def valid_obj_def)
   apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def live_def)
  by (clarsimp simp: state_refs_of_def refs_of_def fun_upd_idem)

(* FIXME copied from Syscall_AI *)
lemmas si_invs = si_invs'[where Q=\<top>,OF hoare_TrueI hoare_TrueI hoare_TrueI hoare_TrueI,simplified]
thm si_invs

lemma send_ipc_invs_for_timeout:
  "\<lbrace>invs and st_tcb_at active tptr and ex_nonz_cap_to tptr
   and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)
   and K (is_ep_cap cap)\<rbrace>
      send_ipc True False (cap_ep_badge cap) True
                 canDonate tptr (cap_ep_ptr cap) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: si_invs simp: obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: ex_nonz_cap_to_def pred_tcb_at_def obj_at_def)
  apply (simp (no_asm) add: cte_wp_at_cases2)
  apply (rule_tac x="tptr" in exI)
  apply (rule_tac x="tcb_cnode_index 4" in exI)
  apply (clarsimp simp: tcb_cnode_map_def)
  apply (clarsimp simp: caps_of_state_tcb_index_trans[OF get_tcb_rev])
  apply (cases cap; simp)
  apply (clarsimp simp: tcb_cnode_map_def cte_wp_at_caps_of_state)
 done

(* FIXME copied from Syscall_AI *)
lemma thread_set_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>ex_nonz_cap_to p\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  apply (clarsimp simp add: ex_nonz_cap_to_def)
  apply (wpsimp wp: hoare_ex_wp thread_set_cte_wp_at_trivial)
  done

lemma send_fault_ipc_invs_timeout:
  "\<lbrace>invs and st_tcb_at active tptr and ex_nonz_cap_to tptr
    and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)
    and K (is_ep_cap cap)\<rbrace>
      send_fault_ipc tptr cap (Timeout badge) canDonate \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wp send_ipc_invs_for_timeout | wpc | clarsimp simp: thread_set_def)+
                apply (wpsimp simp: set_object_def)+
  apply safe
     apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev)
    apply (rule ex_cap_to_after_update, assumption)
    apply (clarsimp simp: obj_at_def get_tcb_SomeD ran_tcb_cap_cases)
   apply (subst caps_of_state_after_update[simplified fun_upd_apply])
    apply (clarsimp simp: obj_at_def get_tcb_SomeD ran_tcb_cap_cases)
   apply (clarsimp simp: caps_of_state_tcb_index_trans tcb_cnode_map_def)
  done

lemma handle_timeout_Timeout_invs:
  "\<lbrace>invs and st_tcb_at active tptr and ex_nonz_cap_to tptr
    and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)\<rbrace>
     handle_timeout tptr (Timeout badge)  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: handle_timeout_def)
  apply (wpsimp simp: handle_timeout_def ran_tcb_cap_cases
      thread_set_def valid_fault_def
      wp: thread_set_invs_trivial send_fault_ipc_invs_timeout)
  apply (case_tac "tcb_timeout_handler y"; clarsimp)
  apply (auto simp: tcb_cnode_map_def caps_of_state_tcb_index_trans)
  done

lemma end_timeslice_invs:
  "\<lbrace>invs and (\<lambda>s. st_tcb_at runnable (cur_thread s) s)
    and (\<lambda>s. caps_of_state s (cur_thread s, tcb_cnode_index 4) = Some (EndpointCap ep b R))
   and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s)\<rbrace>
      end_timeslice t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: end_timeslice_def wp: hoare_drop_imp handle_timeout_Timeout_invs)
  apply safe
    apply (clarsimp simp: st_tcb_at_def obj_at_def invs_def cur_tcb_def is_tcb)
    apply (case_tac "tcb_state tcb"; simp)
   apply simp
  done
thm refill_budget_check_def

lemma schedule_used_non_nil:
  "Suc 0 \<le> length (schedule_used x new)" 
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_Cons:
  "\<exists>r rs. schedule_used x new = r#rs"
  by (induct x; clarsimp simp: Let_def)

lemma refills_budget_check_pos:
  "\<lbrakk>refills_budget_check period usage rfls = (t, ls); Suc 0 \<le> length rfls\<rbrakk>
    \<Longrightarrow> Suc 0 \<le> length ls "
  apply (induct rfls arbitrary: t ls rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (clarsimp simp add: schedule_used_non_nil)
  done

lemma min_budget_check_pos: "Suc 0 \<le> length refills \<Longrightarrow> Suc 0\<le> length (min_budget_merge full refills)"
(* in the C code, this comes at the end of refill_budget_check, where it says
        /* this loop is guaranteed to terminate as the sum of
         * rAmount in a refill must be >= MIN_BUDGET */
we need to prove this. *)
  sorry

lemma invs_valid_refills:
  "\<lbrakk> invs s; ko_at (SchedContext sc n) scptr s\<rbrakk> \<Longrightarrow> Suc 0 \<le> length (sc_refills sc)"
  by (clarsimp dest!: invs_valid_objs elim!: obj_at_valid_objsE simp: valid_obj_def valid_sched_context_def)

lemma refill_budget_check_invs:
  "\<lbrace>invs\<rbrace> refill_budget_check sc_ptr usage capacity \<lbrace>\<lambda>rv. invs\<rbrace>"
apply (clarsimp simp: refill_budget_check_def)

   apply_trace (wpsimp simp: refill_budget_check_def refill_full_def
                refill_size_def split_def
          wp: get_sched_context_wp static_imp_wp
              hoare_vcg_all_lift hoare_vcg_if_lift2)
apply (wpsimp wp: get_refills_wp)
apply (wpsimp wp: get_sched_context_wp)
apply (wpsimp wp: hoare_drop_imp)
apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)
apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_conj_lift split_del: if_split)
apply wpsimp
apply (wpsimp simp: wp: hoare_vcg_all_lift hoare_drop_imp)
apply (wpsimp wp: get_refills_wp)
apply wpsimp+
apply (wpsimp simp: refill_full_def refill_size_def)
apply (wpsimp wp: get_refills_wp)
apply wpsimp+
apply (wpsimp wp: get_sched_context_wp simp: refill_full_def refill_size_def)
sorry


thm charge_budget_def check_budget_def
lemma charge_budget_invs: "\<lbrace>invs\<rbrace> charge_budget capacity consumed canTimeout \<lbrace>\<lambda>rv. invs\<rbrace>"
apply (clarsimp simp: charge_budget_def)
apply (wpsimp wp: end_timeslice_invs gts_wp get_object_wp get_sched_context_wp
hoare_drop_imp get_refills_wp hoare_vcg_all_lift refill_budget_check_invs
 simp: update_sched_context_def set_object_def Let_def set_refills_def)
sorry

lemma check_budget_invs: "\<lbrace>invs\<rbrace> check_budget \<lbrace>\<lambda>rv. invs\<rbrace>"
    by (wpsimp simp: check_budget_def refill_full_def refill_size_def
            wp: get_refills_inv hoare_drop_imp get_sched_context_wp charge_budget_invs)

crunch invs[wp]: tcb_release_remove invs
thm invoke_sched_control_configure_def check_budget_def
lemma invoke_sched_control_configure_invs[wp]:
  "\<lbrace>invs and valid_sched_control_inv i\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (cases i;
     wpsimp simp: invoke_sched_control_configure_def valid_sched_control_inv_def refill_update_def
      split_del: if_split
      wp: commit_time_invs update_sc_badge_invs hoare_vcg_if_lift2 check_budget_invs
         hoare_drop_imp get_sched_context_wp charge_budget_invs)


text {* set_thread_state and schedcontext/schedcontrol invocations *}

lemma sts_idle_thread[wp]:
  "\<lbrace>\<lambda>s. t \<noteq> idle_thread s\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def sc_ntfn_sc_at_def obj_at_def)

lemma sts_sc_ntfn_sc_at:
  "\<lbrace>sc_ntfn_sc_at P scp\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. sc_ntfn_sc_at P scp\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def sc_ntfn_sc_at_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (fastforce simp: obj_at_def)
  done

lemma sts_sc_tcb_sc_at:
  "\<lbrace>sc_tcb_sc_at P scp\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. sc_tcb_sc_at P scp\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def sc_tcb_sc_at_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (fastforce simp add: pred_tcb_at_def obj_at_def)
  done

lemma sts_valid_sched_context_inv:
  "\<lbrace>(\<lambda>s. t \<noteq> cur_thread s) and valid_sched_context_inv sci\<rbrace>
      set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_context_inv sci\<rbrace>"
  apply (cases sci; clarsimp simp: )
      prefer 4
      apply (wpsimp+)[2]
    apply (wpsimp wp: valid_cap_typ set_object_wp gets_the_inv simp: set_thread_state_def
     | clarsimp simp: sc_ntfn_sc_at_def sc_tcb_sc_at_def sc_yf_sc_at_def dest!: get_tcb_SomeD split: cap.split
     | fastforce simp: valid_cap_def sc_ntfn_sc_at_def obj_at_def ran_tcb_cap_cases
                       fun_upd_def get_tcb_def is_tcb sc_tcb_sc_at_def pred_tcb_at_def
                 intro!: ex_cap_to_after_update
                 split: cap.split_asm option.splits kernel_object.split_asm)+
  done

lemma sts_valid_sched_control_inv:
  "\<lbrace>valid_sched_control_inv sci\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_control_inv sci\<rbrace>"
  by (cases sci; wpsimp)

lemma decode_sched_context_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_context_invocation_def whenE_def
                          split del: if_split
            | wp_once hoare_drop_imp get_sk_obj_ref_inv get_sc_obj_ref_inv | wpcw)+
  done

lemma decode_sched_control_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_control_invocation_def whenE_def unlessE_def
                          split del: if_split
            | wp_once hoare_drop_imp get_sk_obj_ref_inv | wpcw)+
  done

lemma decode_sched_context_inv_wf:
  "\<lbrace>invs and sc_at sc_ptr and ex_nonz_cap_to sc_ptr and
     (\<lambda>s. ex_nonz_cap_to (cur_thread s) s) and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>valid_sched_context_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_context_invocation_def whenE_def ethread_get_def
      get_sk_obj_ref_def get_tcb_obj_ref_def get_sc_obj_ref_def
      split_del: if_split
      wp: hoare_vcg_if_splitE get_simple_ko_wp
      thread_get_wp' get_sched_context_wp)
  apply (intro conjI; intro impI allI)
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (rule conjI; intro impI allI)
     apply simp
     apply (erule ballE[where x="hd excaps"])
      prefer 2
      apply (drule hd_in_set, simp)
     apply (erule_tac x=x in ballE)
      apply (clarsimp simp add: obj_at_def sc_ntfn_sc_at_def)
     apply clarsimp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     prefer 2
     apply (drule hd_in_set, simp)
    apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
   apply (frule invs_valid_global_refs, drule invs_valid_objs, clarsimp dest!: idle_no_ex_cap)
 apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (rule conjI; intro impI allI)
    apply simp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     apply (clarsimp simp: obj_at_def sc_ntfn_sc_at_def is_sc_obj_def)
    apply clarsimp
   apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (erule_tac x=x in ballE)
    prefer 2
    apply (drule hd_in_set, simp)
   apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_sc_obj_def is_tcb pred_tcb_at_def sc_yf_sc_at_def)
  done

lemma decode_sched_control_inv_wf:
  "\<lbrace>invs and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>valid_sched_control_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_control_invocation_def whenE_def unlessE_def
      split_del: if_split)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (fastforce simp add: valid_cap_def obj_at_def split: cap.split_asm)
  done




end