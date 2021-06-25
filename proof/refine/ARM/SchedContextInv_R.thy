(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContextInv_R
imports Invocations_R Tcb_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

primrec valid_sc_inv' :: "sched_context_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_inv' (InvokeSchedContextConsumed scptr args) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextBind scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and
             bound_sc_tcb_at' ((=) None) t and
             obj_at' (\<lambda>sc. scTCB sc = None) scptr \<^cancel>\<open> and
             FIXME RT: can hopefully be established via assertions:
             (\<lambda>s. st_tcb_at' (ipc_queued_thread_state) t s
                     \<longrightarrow> sc_at_pred' (sc_released (cur_time s)) scptr s) \<close>
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and
             obj_at' (\<lambda>ntfn. ntfnSc ntfn = None) n and
             obj_at' (\<lambda>sc. scNtfn sc = None) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbindObject scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and obj_at' (\<lambda>sc. scTCB sc = Some t) scptr and
             (\<lambda>s. t \<noteq> ksCurThread s)
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and obj_at' (\<lambda>sc. scNtfn sc = Some n) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbind scptr) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextYieldTo scptr args) =
     (\<lambda>s. ex_nonz_cap_to' scptr s \<and>
          (\<forall>ct. ct = ksCurThread s \<longrightarrow>
                bound_yt_tcb_at' ((=) None) ct s \<and>
                obj_at' (\<lambda>sc. \<exists>t. scTCB sc = Some t \<and> t \<noteq> ct) scptr s))"

definition
  valid_refills_number' :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_refills_number' max_refills n \<equiv> max_refills \<le> refillAbsoluteMax' n"

primrec valid_sc_ctrl_inv' :: "sched_control_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_ctrl_inv' (InvokeSchedControlConfigure scptr budget period mrefills badge) =
     ((\<lambda>s. \<exists>n. sc_at'_n n scptr s \<and> valid_refills_number' mrefills n) and
      ex_nonz_cap_to' scptr and K (MIN_REFILLS \<le> mrefills) and
      K (budget \<le> MAX_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         period \<le> MAX_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         budget \<le> period))"

primrec sc_inv_rel :: "Invocations_A.sched_context_invocation \<Rightarrow> sched_context_invocation \<Rightarrow> bool"
  where
  "sc_inv_rel (Invocations_A.InvokeSchedContextConsumed sc_ptr bf) sci' =
   (sci' = InvokeSchedContextConsumed sc_ptr bf)"
| "sc_inv_rel (Invocations_A.InvokeSchedContextBind sc_ptr cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextBind sc_ptr cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbindObject sc_ptr cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextUnbindObject sc_ptr cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbind sc_ptr) sci' =
   (sci' = InvokeSchedContextUnbind sc_ptr)"
| "sc_inv_rel (Invocations_A.InvokeSchedContextYieldTo sc_ptr bf) sci' =
   (sci' = InvokeSchedContextYieldTo sc_ptr bf)"

primrec sc_ctrl_inv_rel ::
  "Invocations_A.sched_control_invocation \<Rightarrow> sched_control_invocation \<Rightarrow> bool" where
  "sc_ctrl_inv_rel (Invocations_A.InvokeSchedControlConfigure sc_ptr budget period refills badge) sci' =
    (sci' = InvokeSchedControlConfigure sc_ptr budget period refills badge)"

lemma decodeSchedContext_Bind_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContext_Bind sc_ptr excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_Bind_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_UnbindObject_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContext_UnbindObject sc_ptr excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_UnbindObject_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_YieldTo_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s \<and> ex_nonz_cap_to' sc_ptr s\<rbrace>
   decodeSchedContext_YieldTo sc_ptr args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_YieldTo_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp getTCB_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

lemma decodeSchedContextInvocation_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContextInvocation label sc_ptr excaps args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (simp add: decodeSchedContextInvocation_def)
  apply (wpsimp wp: decodeSchedContext_Bind_wf
                    decodeSchedContext_UnbindObject_wf
                    decodeSchedContext_YieldTo_wf)
  apply (fastforce dest: valid_SchedContextCap_sc_at')
  done

lemma decodeSchedControlInvocation_wf:
  "\<lbrace>invs' and (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
    and (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedControlInvocation label args excaps
   \<lbrace>valid_sc_ctrl_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedControlInvocation_def)
  apply (case_tac "genInvocationType label"; simp; (solves wpsimp)?)
  apply (wpsimp simp: decodeSchedControl_Configure_def)
  apply (cases excaps; simp)
  apply (rename_tac a list, case_tac a; simp add: isSchedContextCap_def)
  apply (clarsimp simp: valid_cap'_def  ko_wp_at'_def scBits_simps valid_refills_number'_def
                        MAX_PERIOD_def maxPeriodUs_def usToTicks_def us_to_ticks_mono
                        MIN_BUDGET_def kernelWCET_ticks_def timeArgSize_def minBudgetUs_def
                        MIN_REFILLS_def minRefills_def not_less)
  apply (insert us_to_ticks_mult)
  using kernelWCET_ticks_no_overflow apply clarsimp
  using mono_def apply blast
  done

lemma decodeSchedcontext_Bind_corres:
  "list_all2 cap_relation excaps excaps'
   \<Longrightarrow> corres (ser \<oplus> sc_inv_rel)
         (invs and valid_sched and sc_at sc_ptr and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x))
         (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
         (decode_sched_context_bind sc_ptr excaps)
         (decodeSchedContext_Bind sc_ptr excaps')"
  apply (clarsimp simp: decode_sched_context_bind_def decodeSchedContext_Bind_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply (corressimp simp: sc_relation_def)
  apply (case_tac cap; clarsimp)
   apply (clarsimp simp: bindE_assoc)
   apply (rule corres_splitEE''[where r'="(=)"]; (solves wpsimp)?)
    apply (corressimp corres: get_ntfn_corres
                        simp: get_sk_obj_ref_def ntfn_relation_def valid_cap_def valid_cap'_def
                          wp: hoare_vcg_all_lift)
   apply (rule corres_splitEE_skip; (solves wpsimp)?)
    apply (corressimp corres: get_ntfn_corres
                        simp: get_sk_obj_ref_def sc_relation_def)
   apply (clarsimp simp: returnOk_def)
  apply (clarsimp simp: bindE_assoc get_tcb_obj_ref_def)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadget_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply (clarsimp simp: valid_cap_def)
     apply (clarsimp simp: valid_cap'_def)
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; (solves \<open>wpsimp simp: valid_cap'_def obj_at'_def\<close>)?)
   apply (corressimp corres: get_ntfn_corres
                       simp: get_sk_obj_ref_def sc_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule corres_splitEE)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (clarsimp simp: returnOk_def)
         apply (subst corres_liftE_rel_sum)
         apply (rule corres_rel_imp)
          apply (rule gts_isBlocked_corres)
         apply simp
        apply wpsimp
       apply wpsimp
      apply (rule corres_liftE_rel_sum[THEN iffD2, OF get_sc_released_corres])
     apply wpsimp
    apply (wpsimp simp: scReleased_def scActive_def)
   apply (fastforce simp: obj_at_def is_tcb_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma decodeSchedContext_UnbindObject_corres:
  "list_all2 cap_relation excaps excaps'
   \<Longrightarrow> corres (ser \<oplus> sc_inv_rel)
         (invs and sc_at sc_ptr)
         invs'
         (decode_sched_context_unbind_object sc_ptr excaps)
         (decodeSchedContext_UnbindObject sc_ptr excaps')"
  apply (clarsimp simp: decode_sched_context_unbind_object_def decodeSchedContext_UnbindObject_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (case_tac cap; clarsimp)
   apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
   apply (rule corres_splitEE'')
      apply (corressimp corres: get_sc_corres)
      apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
     apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
    apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
   apply (corressimp simp: sc_relation_def)
   apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp simp: sc_relation_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply (rule corres_splitEE'')
     apply (corressimp corres: gct_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply corressimp
  done

lemma decodeSchedContext_YieldTo_corres:
  "corres (ser \<oplus> sc_inv_rel)
          (invs and sc_at sc_ptr)
          invs'
          (decode_sched_context_yield_to sc_ptr args')
          (decodeSchedContext_YieldTo sc_ptr args')"
  apply (clarsimp simp: decode_sched_context_yield_to_def decodeSchedContext_YieldTo_def)
  apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp simp: sc_relation_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply (rule corres_splitEE'')
     apply (corressimp corres: gct_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply (corressimp simp: sc_relation_def)
  apply (clarsimp simp: sc_relation_def)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadget_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply (fastforce dest: invs_valid_objs valid_objs_ko_at
                       simp: valid_obj_def valid_sched_context_def)
     apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                      simp: valid_sched_context'_def)
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadget_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply fastforce
     apply fastforce
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadget_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply fastforce
     apply fastforce
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma decode_sc_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_inv_rel)
          (invs and valid_sched and sc_at sc_ptr and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x))
          (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
          (decode_sched_context_invocation (mi_label mi) sc_ptr excaps args')
          (decodeSchedContextInvocation (mi_label mi) sc_ptr excaps' args')"
  apply (clarsimp simp: decode_sched_context_invocation_def decodeSchedContextInvocation_def
             split del: if_split)
  apply (cases "gen_invocation_type (mi_label mi)"
         ; clarsimp split: gen_invocation_labels.split list.splits
                split del: if_split)
      apply (clarsimp simp: returnOk_def)
     apply (corressimp corres: decodeSchedcontext_Bind_corres)
    defer
    apply (corressimp corres: decodeSchedContext_UnbindObject_corres)
   apply (corressimp corres: decodeSchedContext_YieldTo_corres)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp corres: gct_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (clarsimp simp: sc_relation_def)
  done

lemma decode_sc_ctrl_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_ctrl_inv_rel) \<top> \<top>
          (decode_sched_control_invocation (mi_label mi) args' excaps)
          (decodeSchedControlInvocation (mi_label mi) args' excaps')"
  apply (clarsimp simp: decode_sched_control_invocation_def decodeSchedControlInvocation_def)
  apply (cases "gen_invocation_type (mi_label mi)"
         ; clarsimp simp: decodeSchedControl_Configure_def TIME_ARG_SIZE_def timeArgSize_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply corressimp
  apply (rule corres_splitEE'')
      apply corressimp
     apply (case_tac cap; clarsimp simp: isSchedContextCap_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply corressimp
  apply (auto simp: minBudgetUs_def MIN_BUDGET_US_def maxPeriodUs_def parse_time_arg_def
                    parseTimeArg_def usToTicks_def minRefills_def MIN_REFILLS_def
                    max_num_refills_eq_refillAbsoluteMax' refillAbsoluteMax_def max_refills_cap_def
             split: cap.splits)
  done

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma invoke_sched_context_corres:
  "sc_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres (=)
          (einvs and valid_sched_context_inv sc_inv and simple_sched_action and ct_active)
          (invs' and sch_act_simple and valid_sc_inv' sc_inv' and ct_active')
          (invoke_sched_context sc_inv)
          (invokeSchedContext sc_inv')"
  apply (simp add: invoke_sched_context_def invokeSchedContext_def)
  (* most of the next layer down should go into SchedContext_R, because some of these are
     reused in Finalise and IpcCancel *)
  sorry

lemma refill_new_bundled:
   "refill_new sc_ptr max_refills budget period
    = (do cur_time \<leftarrow> gets cur_time;
          set_sc_obj_ref sc_period_update sc_ptr period;
          set_sc_obj_ref sc_budget_update sc_ptr budget;
          update_sched_context sc_ptr (\<lambda>sc. sc\<lparr>sc_refill_max := max_refills,
                                               sc_refills := [\<lparr>r_time = cur_time, r_amount = budget\<rparr>]\<rparr>);
          maybe_add_empty_tail sc_ptr
       od)"
  unfolding refill_new_def
            update_sched_context_decompose_ext2[where f=sc_refills_update and g=sc_refill_max_update]
            update_sched_context_decompose_ext2[where f=sc_refill_max_update and g=sc_budget_update]
            update_sched_context_decompose_ext2[where f=sc_budget_update and g=sc_period_update]
  apply (simp add: bind_assoc)
  done

lemma refillNew_bundled:
  "monadic_rewrite False True (sc_at' scPtr)
   (refillNew scPtr maxRefills budget period)
   (do curTime \<leftarrow> getCurTime;
       sc \<leftarrow> getSchedContext scPtr;
       setSchedContext scPtr (scPeriod_update (\<lambda>_. period) sc);
       sc \<leftarrow> getSchedContext scPtr;
       setSchedContext scPtr (scBudget_update (\<lambda>_. budget) sc);
       sc \<leftarrow> getSchedContext scPtr;
       setSchedContext scPtr (scRefills_update (\<lambda>_. replaceAt 0 (scRefills sc) (Refill curTime budget))
                              (scRefillMax_update (\<lambda>_. maxRefills)
                               (scRefillCount_update (\<lambda>_. 1)
                                (scRefillHead_update (\<lambda>_. 0) sc))));
       maybeAddEmptyTail scPtr
    od)"
  apply (clarsimp simp: refillNew_def)
  apply (rule monadic_rewrite_bind_tail[rotated])
   apply (fastforce simp: getCurTime_def intro: gets_inv)
  apply (rule monadic_rewrite_bind_tail[rotated, OF get_sc_inv'])
  apply (rule monadic_rewrite_bind_tail[rotated, OF set_sc'.typ_at_lifts'(6)])
  apply (rule monadic_rewrite_bind_tail[rotated, OF get_sc_inv'])
  apply (rule monadic_rewrite_bind_tail[rotated, OF set_sc'.typ_at_lifts'(6)])
  apply (simp flip: bind_assoc)
  apply (rule monadic_rewrite_bind_head)
  apply (simp add: bind_assoc)
  apply (subst bind_assoc_group4)
  apply (rule monadic_rewrite_rewrite_head)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose_decompose_ext2[unfolded K_bind_def])
   apply (clarsimp simp: objBits_simps)
  apply (simp only: bind_assoc)
  apply (subst bind_assoc_group4)
  apply (rule monadic_rewrite_rewrite_head)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose_decompose_ext2[unfolded K_bind_def])
   apply (clarsimp simp: objBits_simps)
  apply (simp only: bind_assoc)
  apply (clarsimp simp: setRefillHd_def updateRefillHd_def bind_assoc)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans_dup)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose[unfolded K_bind_def])
   apply (rule monadic_rewrite_refl3)
   apply clarsimp
  apply (fastforce simp: objBits_simps length_replaceAt)
  done

lemma getCurTime_sp:
  "\<lbrace>P\<rbrace> getCurTime \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurTime s)\<rbrace>"
  by (wpsimp simp: getCurTime_def)

lemma isRoundRobin_corres:
  "corres (=) (pspace_aligned and pspace_distinct and sc_at sc_ptr) \<top>
              (is_round_robin sc_ptr) (isRoundRobin sc_ptr)"
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (clarsimp simp: is_round_robin_def isRoundRobin_def)
  apply (corressimp corres: get_sc_corres
                      simp: sc_relation_def)
  done

lemma refillAddTail_corres:
  "time = time' \<and> amount = amount'
   \<Longrightarrow> corres dc (pspace_aligned and pspace_distinct and sc_at sc_ptr)
                 (obj_at' (\<lambda>sc'. scRefillHead sc' < scRefillMax sc' \<and> 0 < scRefillCount sc'
                                 \<and> scRefills sc' \<noteq> [] \<and> scRefillCount sc' < scRefillMax sc'
                                 \<and> scRefillMax sc' \<le> length (scRefills sc')) sc_ptr)
                 (refill_add_tail sc_ptr \<lparr>r_time = time, r_amount = amount\<rparr>)
                 (refillAddTail sc_ptr (Refill time' amount'))"
  (is "_ \<Longrightarrow> corres _ _ (obj_at' (\<lambda>sc'. ?pred sc') sc_ptr) _ _")
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (clarsimp simp: refill_add_tail_def refillAddTail_def getRefillNext_getSchedContext
                        getRefillSize_def2 liftM_def get_refills_def)

  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (rename_tac sc')

  apply (rule corres_symb_exec_r[OF _ gets_the_sp, rotated]; (solves wpsimp)?)+
   apply (rule no_ofail_gets_the, wp no_ofail_readSchedContext, clarsimp)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def readSchedContext_def dest!: readObject_misc_ko_at')
  apply (clarsimp simp: pred_conj_def cong: conj_cong)
  apply (clarsimp simp: set_refills_def)

  apply (clarsimp simp: update_sched_context_def bind_assoc)
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply (wpsimp simp: obj_at_def cong: conj_cong)

  apply (rename_tac obj)
  apply (case_tac obj
         ; clarsimp
         ; (solves \<open>(corressimp corres: corres_False simp: obj_at_def is_sc_obj_def
                     | intro conjI)+\<close>)?)

  supply if_split[split del]
  apply (rule corres_symb_exec_r[rotated, OF assert_inv]; (solves wpsimp)?)
   apply wpsimp
   apply (simp add: obj_at'_def projectKOs)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)

  apply (rule_tac F="?pred sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (rule corres_guard_imp)
    apply (rule_tac f="\<lambda>sc'. sc'\<lparr>sc_refills := sc_refills sc @ [\<lparr>r_time = time', r_amount = amount'\<rparr>]\<rparr>"
                and f'="\<lambda>sc''. scRefillCount_update (\<lambda>_. Suc (scRefillCount sc'))
                                (scRefills_update
                                 (\<lambda>_. replaceAt (if refillTailIndex sc' = scRefillMax sc' - Suc 0
                                                    then 0
                                                    else Suc (refillTailIndex sc'))
                                                (scRefills sc') (Refill time' amount')) sc'')"
                 in setSchedContext_no_stack_update_corres)
       apply (simp add: sc_relation_def)
       apply (intro conjI impI)
        apply (clarsimp simp: refills_map_def)
        apply (subst wrap_slice_append)
           apply linarith
          apply simp
         apply (fastforce simp: refillTailIndex_def length_replaceAt)
        apply (prop_tac "map refill_map (wrap_slice (scRefillHead sc') (scRefillCount sc')
                                                    (scRefillMax sc') (scRefills sc'))
                         = map refill_map (wrap_slice (scRefillHead sc') (scRefillCount sc')
                                                      (scRefillMax sc')
                                                      (replaceAt (if refillTailIndex sc' = scRefillMax sc' - Suc 0
                                                                     then 0
                                                                     else Suc (refillTailIndex sc'))
                                                                 (scRefills sc')
                                                                 (Refill time' amount')))")
         apply (rule subst[OF wrap_slice_replaceAt_eq]; simp?)
          apply (fastforce simp: refillTailIndex_def Let_def split: if_splits)
         apply (fastforce simp: refill_map_def refillTailIndex_def Let_def split: if_splits)
        apply (clarsimp simp: refill_map_def refillTailIndex_def split: if_splits)
         apply (fastforce simp: replaceAt_index)
        apply (clarsimp simp: Let_def split: if_splits)
         apply (prop_tac "Suc (scRefillHead sc' + scRefillCount sc' - Suc (scRefillMax sc'))
                          = scRefillHead sc' + scRefillCount sc' - scRefillMax sc'")
          apply linarith
         apply (fastforce simp: replaceAt_index)
        apply (fastforce simp: replaceAt_index)
       apply (fastforce simp: refillTailIndex_def Let_def)
     apply (fastforce simp: objBits_simps)
    apply fastforce
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma isRoundRobin_sp:
  "\<lbrace>P\<rbrace>
   isRoundRobin scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = (scPeriod sc = 0))\<rbrace>"
  apply (simp add: isRoundRobin_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma maybeAddEmptyTail_corres:
  "corres dc
          (pspace_aligned and pspace_distinct and valid_objs and is_active_sc sc_ptr
           and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
          (\<lambda>s'. obj_at' (\<lambda>sc'. scRefillHead sc' < scRefillMax sc' \<and> 0 < scRefillCount sc'
                                \<and> scRefills sc' \<noteq> [] \<and> scRefillCount sc' < scRefillMax sc'
                                \<and> scRefillMax sc' \<le> length (scRefills sc')) sc_ptr s'
                \<and> valid_objs' s')
          (maybe_add_empty_tail sc_ptr)
          (maybeAddEmptyTail sc_ptr)"
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel])
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def vs_all_heap_simps)
  apply (clarsimp simp: maybe_add_empty_tail_def maybeAddEmptyTail_def get_refills_def)
  apply (rule corres_split'[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corressimp corres: isRoundRobin_corres)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def vs_all_heap_simps)
  apply (clarsimp simp: when_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def vs_all_heap_simps)
  apply (rename_tac sc')
  apply (corressimp corres: refillAddTail_corres)
  apply (frule refill_hd_relation; clarsimp simp: obj_at'_def)
  apply (fastforce dest: valid_objs_valid_sched_context_size
                   simp: obj_at_def is_sc_obj_def vs_all_heap_simps refill_map_def)
  done

lemma getRefills_sp:
  "\<lbrace>P\<rbrace>
   getRefills scPtr
   \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> (rv = scRefills sc))\<rbrace>"
  apply (simp add: getRefills_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule get_sc_sp')
  apply (wp hoare_return_sp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma updateRefillHd_corres:
  "\<lbrakk>sc_ptr = scPtr;
    \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = (refill_map (f' refill'))\<rbrakk>
   \<Longrightarrow> corres dc
              (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
               and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
              valid_objs'
              (update_refill_hd sc_ptr f)
              (updateRefillHd scPtr f')"
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel])
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (clarsimp simp: update_refill_hd_def get_refills_def set_refills_def updateRefillHd_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (clarsimp simp: update_sched_context_def)
  apply (rename_tac sc' n)
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid simp: obj_at_def)
   apply (wpsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj
         ; clarsimp; (solves \<open>corressimp corres: corres_False simp: obj_at_def is_sc_obj_def\<close>)?)
  apply (rename_tac abs_sc abs_n)
  apply (rule_tac F="abs_sc = sc" in corres_req)
   apply (clarsimp intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def sc_at_pred_n_def)
  apply clarsimp
  apply (rule_tac F="sc_refills sc \<noteq> []" in corres_req)
   apply (clarsimp intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def sc_at_pred_n_def)

  apply (rule_tac F="0 < scRefillCount sc' \<and> scRefillCount sc' \<le> scRefillMax sc'
                     \<and> scRefillHead sc' < scRefillMax sc'
                     \<and> scRefillMax sc' \<le> length (scRefills sc')
                     \<and> MIN_REFILLS \<le> length (scRefills sc')"
               in corres_req)
   apply (prop_tac "sc_relation sc n sc'")
    apply (fastforce dest: state_relation_pspace_relation)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def refills_map_def sc_relation_def)

  apply (rule corres_guard_imp)
    apply (rule_tac f="\<lambda>sc'. sc\<lparr>sc_refills := f (refill_hd sc) # tl (sc_refills sc)\<rparr>"
                and f'="\<lambda>sc''. scRefills_update (\<lambda>_. replaceAt (scRefillHead sc') (scRefills sc')
                                                                (f' (refillHd sc'))) sc''"
                 in setSchedContext_no_stack_update_corres)
       apply (clarsimp simp: sc_relation_def)
       apply (case_tac "sc_refills sc = []")
        apply clarsimp
        apply (prop_tac "scRefills sc' \<noteq> []")
         apply clarsimp
        apply (rule nth_equalityI)
         apply (fastforce simp: refills_map_def)

        apply (case_tac "i=0")
         apply (clarsimp simp: refills_map_def)
         apply (subst hd_map, fastforce)
         apply (subst hd_wrap_slice; simp)
         apply (rule_tac f=refill_map in arg_cong)
         apply (subst wrap_slice_index; simp?)
         apply (fastforce simp: refillHd_def replaceAt_index)
        apply (clarsimp simp: refills_map_def nth_tl)
        apply (rule_tac f=refill_map in arg_cong)
        apply (rule_tac P="\<lambda>t. _ = t" in ssubst)
         apply (erule (1) wrap_slice_index)
         apply simp+
        apply (fastforce simp: replaceAt_index wrap_slice_index)
      apply fastforce
     apply (clarsimp simp: objBits_simps obj_at_def)+
  done

lemma updateRefillTl_corres:
  "\<lbrakk>sc_ptr = scPtr;
    \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = (refill_map (f' refill'))\<rbrakk>
   \<Longrightarrow> corres dc
              (pspace_aligned and pspace_distinct and sc_at sc_ptr and active_sc_at sc_ptr
               and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
              valid_objs'
              (update_refill_tl sc_ptr f)
              (updateRefillTl scPtr f')"
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel])
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (clarsimp simp: update_refill_tl_def get_refills_def set_refills_def updateRefillTl_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (clarsimp simp: update_sched_context_def)
  apply (rename_tac sc' n)
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid simp: obj_at_def)
   apply (wpsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj
         ; clarsimp; (solves \<open>corressimp corres: corres_False simp: obj_at_def is_sc_obj_def\<close>)?)
  apply (rename_tac abs_sc abs_n)
  apply (rule_tac F="abs_sc = sc" in corres_req)
   apply (clarsimp intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def sc_at_pred_n_def)
  apply clarsimp
  apply (rule_tac F="sc_refills sc \<noteq> []" in corres_req)
   apply (clarsimp intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def sc_at_pred_n_def)

  apply (rule_tac F="0 < scRefillCount sc' \<and> scRefillCount sc' \<le> scRefillMax sc'
                     \<and> scRefillHead sc' < scRefillMax sc'
                     \<and> scRefillMax sc' \<le> length (scRefills sc')
                     \<and> MIN_REFILLS \<le> length (scRefills sc')"
               in corres_req)
   apply (prop_tac "sc_relation sc n sc'")
    apply (fastforce dest: state_relation_pspace_relation)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def refills_map_def sc_relation_def)

  apply (rule corres_guard_imp)
    apply (rule_tac f="\<lambda>sc'. sc'\<lparr>sc_refills := butlast (sc_refills sc) @ [f (refill_tl sc)]\<rparr>"
                and f'="\<lambda>sc''. scRefills_update
                 (\<lambda>_. replaceAt (refillTailIndex sc') (scRefills sc')
                        (f' (refillTl sc'))) sc''"
                 in setSchedContext_no_stack_update_corres)
       apply (clarsimp simp: sc_relation_def)
       apply (case_tac "sc_refills sc = []")
        apply clarsimp
        apply (prop_tac "scRefills sc' \<noteq> []", clarsimp)

        apply (rule nth_equalityI)
         apply (fastforce simp: refills_map_def length_replaceAt)

        apply (case_tac "i = length (sc_refills sc) - 1")

         apply (prop_tac "(butlast (refills_map (scRefillHead sc') (scRefillCount sc') (scRefillMax sc')
                                                (scRefills sc'))
                           @ [f (last (refills_map (scRefillHead sc') (scRefillCount sc')
                                                   (scRefillMax sc') (scRefills sc')))])
                          ! i
                          = f (last (refills_map (scRefillHead sc') (scRefillCount sc')
                                                 (scRefillMax sc') (scRefills sc')))")
          apply (clarsimp simp: refills_map_def)
          apply (prop_tac "length (butlast (map refill_map (wrap_slice (scRefillHead sc')
                                                                       (scRefillCount sc')
                                                                       (scRefillMax sc')
                                                                       (scRefills sc'))))
                           = scRefillCount sc' - 1")
           apply fastforce
          apply (metis One_nat_def nth_append_length)

         apply (clarsimp simp: refills_map_def)
         apply (subst wrap_slice_index; simp?)
         apply (clarsimp simp: refillTailIndex_def refillTl_def replaceAt_index)
         apply (subst last_conv_nth, fastforce)+
         apply simp
         apply (subst wrap_slice_index; simp)+

        \<comment> \<open>i \<noteq> length (sc_refills sc) - 1\<close>
        apply (prop_tac "(butlast (refills_map (scRefillHead sc') (scRefillCount sc')
                                               (scRefillMax sc') (scRefills sc'))
                          @ [f (last (refills_map (scRefillHead sc') (scRefillCount sc')
                                                  (scRefillMax sc') (scRefills sc')))])
                         ! i
                         = refills_map (scRefillHead sc') (scRefillCount sc')
                                       (scRefillMax sc') (scRefills sc')
                           ! i")
         apply (prop_tac " i < length (butlast (refills_map (scRefillHead sc') (scRefillCount sc')
                                                            (scRefillMax sc') (scRefills sc')))")
          apply (subst length_butlast)
          apply (fastforce simp: refills_map_def)
         apply (simp add: nth_append nth_butlast)
        apply (clarsimp simp: refills_map_def)
        apply (rule_tac f=refill_map in arg_cong)
        apply (subst wrap_slice_index; simp)
        apply (intro conjI impI)
         apply (subst wrap_slice_index; simp?)
         apply (fastforce simp: refillTailIndex_def Let_def replaceAt_index split: if_splits)
        apply (subst wrap_slice_index; simp?)
        apply (fastforce simp: refillTailIndex_def Let_def replaceAt_index split: if_splits)
      apply fastforce
     apply (clarsimp simp: objBits_simps length_replaceAt)
    apply simp
   apply (clarsimp simp: obj_at_def)
  apply simp
  done

lemma getCurSc_sp:
  "\<lbrace>P\<rbrace>
   getCurSc
   \<lbrace>\<lambda>rv s. P s \<and> rv = ksCurSc s\<rbrace>"
  apply (simp add: getCurSc_def)
  apply (wpsimp wp: hoare_return_sp)
  done

lemma active_sc_at'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; is_active_sc sc_ptr s;
    sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps active_sc_at'_def obj_at'_def projectKOs
                        active_sc_def)
  done

lemma refillBudgetCheckRoundRobin_corres:
  "corres dc
          (\<lambda>s. pspace_aligned s \<and> pspace_distinct s \<and> active_sc_valid_refills s \<and> cur_sc_active s
               \<and> valid_objs s)
          valid_objs'
          (refill_budget_check_round_robin usage) (refillBudgetCheckRoundRobin usage)"
  apply (clarsimp simp: refill_budget_check_round_robin_def refillBudgetCheckRoundRobin_def)
  apply (rule corres_split'[rotated 2, OF gets_sp getCurSc_sp])
   apply (corressimp corres: getCurSc_corres)

  apply (rule_tac Q="\<lambda>s. active_sc_at' (ksCurSc s) s" in corres_cross_add_guard)
   apply (rule_tac sc_ptr="ksCurSc s'" in active_sc_at'_cross, simp+)
    apply (fastforce dest: valid_objs_valid_sched_context_size )
   apply (fastforce dest: valid_objs_valid_sched_context_size
                    simp: vs_all_heap_simps obj_at_def is_sc_obj_def)

  apply (rule_tac Q="\<lambda>_ s. pspace_aligned s \<and> pspace_distinct s \<and> cur_sc_active s \<and> sc_at scPtr s
                           \<and> cur_sc s = scPtr \<and> sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) scPtr s"
              and Q'="\<lambda>_ s. valid_objs' s"
               in corres_split'[rotated 2])
     apply ((wpsimp wp: get_refills_wp simp: update_refill_hd_def | wpsimp wp: set_refills_wp)+)[1]
     apply (fastforce intro: valid_objs_valid_sched_context_size
                       simp: obj_at_def is_sc_obj_def sc_at_pred_n_def vs_all_heap_simps)

    apply (wpsimp wp: updateRefillHd_valid_objs')
   apply (rule corres_guard_imp)
     apply (rule_tac f="\<lambda>refill. refill\<lparr>r_amount := r_amount refill - usage\<rparr>"
                 and f'="\<lambda>r. rAmount_update (\<lambda>_. rAmount r - usage) r"
                  in updateRefillHd_corres)
      apply simp
     apply (clarsimp simp: refill_map_def)
    apply (fastforce intro: valid_objs_valid_sched_context_size
                      simp: active_sc_valid_refills_def valid_refills_def vs_all_heap_simps
                            rr_valid_refills_def obj_at_kh_kheap_simps is_sc_obj_def)
   apply simp
  apply (rule corres_guard_imp)
    apply (rule_tac f="\<lambda>refill. refill\<lparr>r_amount := r_amount refill + usage\<rparr>"
                and f'="\<lambda>r. rAmount_update (\<lambda>_. rAmount r + usage) r"
                 in updateRefillTl_corres)
     apply simp
    apply (clarsimp simp: refill_map_def)
   apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def)
  apply simp
  done

lemma refillResetRR_corres:
  "csc_ptr = cscPtr
   \<Longrightarrow> corres dc (pspace_aligned and pspace_distinct and sc_at csc_ptr and is_active_sc csc_ptr
                  and round_robin csc_ptr and valid_refills csc_ptr)
                 valid_objs'
                 (refill_reset_rr csc_ptr) (refillResetRR cscPtr)"
  (is "_ \<Longrightarrow> corres dc ?abs ?conc _ _")
  apply (rule corres_cross[where Q' = "sc_at' cscPtr", OF sc_at'_cross_rel])
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (clarsimp simp: refill_reset_rr_def refillResetRR_def get_refills_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (rename_tac sc')

  apply (rule_tac F="rr_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_budget sc)
                     \<and> 0 < scRefillCount sc' \<and> scRefillCount sc' \<le> scRefillMax sc'
                     \<and> scRefillHead sc' < scRefillMax sc'
                     \<and> scRefillMax sc' \<le> length (scRefills sc') \<and> scRefills sc' \<noteq> []"
               in corres_req)
   apply clarsimp
   apply (prop_tac "sc_relation sc n sc'")
    apply (fastforce dest: state_relation_pspace_relation
                     simp: pspace_relation_def vs_all_heap_simps)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_refills_def vs_all_heap_simps round_robin_def obj_at_def
                          active_sc_def valid_sched_context'_def sc_relation_def)

  apply (rule_tac Q="\<lambda>_ s. pspace_aligned s \<and> pspace_distinct s \<and> sc_at cscPtr s
                           \<and> active_sc_at cscPtr s
                           \<and> rr_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_budget sc)
                           \<and> sc_refills_sc_at (\<lambda>refills. length refills = 2) cscPtr s"
              and Q'="\<lambda>_. ?conc and sc_at' cscPtr"
               in corres_split'[rotated 2, where r'="dc"])
     apply (clarsimp simp: pred_conj_def)
     apply (intro hoare_vcg_conj_lift_pre_fix
            ; (solves \<open>wpsimp simp: set_refill_hd_def update_refill_hd_def\<close>)?)
      apply (wpsimp simp: set_refill_hd_def update_refill_hd_def)
      apply (clarsimp simp: obj_at_def vs_all_heap_simps)
     apply (wpsimp wp: set_refills_wp get_refills_wp
                 simp: set_refill_hd_def update_refill_hd_def)
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def rr_valid_refills_def)
    apply (wpsimp simp: setRefillHd_def updateRefillHd_def)
    apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                     simp: valid_sched_context'_def length_replaceAt valid_sched_context_size'_def
                           scBits_simps objBits_simps)

   apply (clarsimp simp: set_refill_hd_def setRefillHd_def)
   apply (rule corres_guard_imp)
     apply (rule_tac f="\<lambda>_. \<lparr>r_time = r_time (refill_hd sc),
                             r_amount = r_amount (refill_hd sc)
                                        + r_amount (hd (tl (sc_refills sc)))\<rparr>"
                 and f'="\<lambda>r. Refill (rTime (refillHd sc'))
                                    (rAmount (refillHd sc') + rAmount (refillTl sc'))"
                  in updateRefillHd_corres)
      apply simp
     apply (clarsimp simp: refill_map_def)
     apply (frule refill_hd_relation, clarsimp)
     apply (prop_tac "length (sc_refills sc) = 2")
      apply (clarsimp simp: rr_valid_refills_def)
     apply (intro conjI impI)
      apply (fastforce dest: refills_tl_equal
                       simp: refill_map_def)
     apply (fastforce dest: refills_tl_equal
                      simp: refill_map_def hd_drop_length_2_last)
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def rr_valid_refills_def)
   apply simp

  apply (rule corres_guard_imp)
    apply (clarsimp simp: set_refill_tl_def setRefillTl_def)
    apply (rule_tac f="(\<lambda>_. \<lparr>r_time = r_time (hd (tl (sc_refills sc))), r_amount = 0\<rparr>)"
                and f'="(\<lambda>r. Refill (rTime (refillTl sc')) 0)"
                 in updateRefillTl_corres)
     apply simp
    apply (fastforce dest: refills_tl_equal
                     simp: refill_map_def hd_drop_length_2_last rr_valid_refills_def)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply simp
  done

lemma refillPopHead_corres:
  "sc_ptr = scPtr
   \<Longrightarrow> corres (\<lambda>refill refill'. refill = refill_map refill')
              (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
               and sc_refills_sc_at (\<lambda>refills. 1 < length refills) sc_ptr)
              valid_objs'
              (refill_pop_head sc_ptr) (refillPopHead scPtr)"
  (is "_ \<Longrightarrow> corres _ ?abs ?conc _ _")
  supply if_split[split del]
  apply (rule corres_cross[where Q' = "sc_at' scPtr", OF sc_at'_cross_rel])
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (clarsimp simp: refill_pop_head_def refillPopHead_def)
  apply (clarsimp simp: getRefillNext_getSchedContext get_refills_def liftM_def)

  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)

  apply (rename_tac sc')
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)

  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)

  apply (clarsimp simp: set_refills_def)
  apply (clarsimp simp: update_sched_context_def bind_assoc)
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply (wpsimp simp: obj_at_def)

  apply (rename_tac obj)
  apply (case_tac obj
         ; clarsimp
         ; (solves \<open>(corressimp corres: corres_False simp: obj_at_def is_sc_obj_def
                     | intro conjI)+\<close>)?)

  apply (rename_tac abs_sc n')
  apply (rule_tac F="abs_sc = sc" in corres_req)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)

  apply (clarsimp simp: updateSchedContext_def bind_assoc)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)

  apply (rule_tac F="1 < scRefillCount sc' \<and> scRefillCount sc' \<le> scRefillMax sc'
                     \<and> scRefillHead sc' < scRefillMax sc'
                     \<and> scRefillMax sc' \<le> length (scRefills sc') \<and> scRefills sc' \<noteq> []"
               in corres_req)
   apply (prop_tac "sc_relation sc n sc'")
    apply (fastforce dest: state_relation_pspace_relation)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def sc_relation_def sc_at_pred_n_def obj_at_def
                          refills_map_def)

  apply (rule_tac Q="\<lambda>_. pspace_aligned and pspace_distinct and sc_at sc_ptr and active_sc_at sc_ptr
                         and sc_refills_sc_at (\<lambda>refills. 0 < length refills) sc_ptr"
              and Q'="\<lambda>_. ?conc"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule_tac f="\<lambda>sc. sc\<lparr>sc_refills := tl (sc_refills sc)\<rparr>"
                   and f'="\<lambda>sc''. scRefillCount_update (\<lambda>_. scRefillCount sc' - Suc 0)
                                   (scRefillHead_update (\<lambda>_. if scRefillHead sc' = scRefillMax sc' - Suc 0
                                                                then 0
                                                                else Suc (scRefillHead sc')) sc'')"
                    in setSchedContext_no_stack_update_corres)
          apply (prop_tac "tl (sc_refills sc) = drop (Suc 0) (sc_refills sc)")
           apply (clarsimp simp: sc_relation_def drop_Suc)
          apply (clarsimp simp: sc_relation_def refills_map_def)
          apply (rule nth_equalityI)
           apply (subst length_map)
           apply (subst length_wrap_slice; simp)
          apply (subst nth_map)
           apply (subst length_wrap_slice; simp)
          apply (subst wrap_slice_index; simp)
           apply (fastforce split: if_splits)
          apply (subst wrap_slice_index; simp)
          apply (clarsimp split: if_splits)
         apply simp
        apply (clarsimp simp: objBits_simps)
       apply simp
      apply (clarsimp simp: obj_at_def)
     apply simp
    apply (fastforce dest: refill_hd_relation)
   apply wpsimp
    apply (wpsimp wp: set_object_wp)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def is_sc_obj_def vs_all_heap_simps)
   apply (metis Nitpick.size_list_simp(2) length_ineq_not_Nil(1) less_not_refl3)
  apply wpsimp
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def scBits_simps
                         objBits_simps
                  split: if_splits)
  done

lemma refillNew_corres:
  "1 < max_refills
   \<Longrightarrow> corres dc
             (valid_objs and pspace_aligned and pspace_distinct and sc_at sc_ptr)
             (\<lambda>s'. \<exists>n. sc_at'_n n sc_ptr s' \<and> valid_refills_number' max_refills n \<and> valid_objs' s')
             (refill_new sc_ptr max_refills budget period)
             (refillNew sc_ptr max_refills budget period)"
  (is "_ \<Longrightarrow> corres _ ?abs ?conc _ _")
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (subst refill_new_bundled)
  apply (rule monadic_rewrite_corres'
               [where P'=P' and Q=P' for P', simplified pred_conj_def, simplified, rotated])
   apply (rule monadic_rewrite_imp)
    apply (rule refillNew_bundled)
   apply simp

  apply (rule corres_split'[OF _ _ gets_sp getCurTime_sp])
   apply corressimp
  apply clarsimp
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>_. ?abs" and Q'="\<lambda>_. ?conc and sc_at' sc_ptr" in corres_split'[rotated 2]
         ; (solves wpsimp)?)
     apply (wpsimp wp: update_sched_context_valid_objs_update)
     apply (fastforce dest: valid_objs_ko_at
                      simp: valid_obj_def valid_sched_context_def)
    apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift)
    apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
   apply (corressimp corres: update_sc_no_reply_stack_update_ko_at'_corres
                               [where f'="scPeriod_update (\<lambda>_. period)"]
                       simp: sc_relation_def objBits_simps)

  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>_. ?abs" and Q'="\<lambda>_. ?conc and sc_at' sc_ptr" in corres_split'[rotated 2]
         ; (solves wpsimp)?)
     apply (wpsimp wp: update_sched_context_valid_objs_update)
     apply (fastforce dest: valid_objs_ko_at
                      simp: valid_obj_def valid_sched_context_def)
    apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift)
    apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
   apply (corressimp corres: update_sc_no_reply_stack_update_ko_at'_corres
                               [where f'="scBudget_update (\<lambda>_. budget)"]
                       simp: sc_relation_def objBits_simps)

  apply (clarsimp simp: update_sched_context_def bind_assoc)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc')
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid simp: obj_at_def)
   apply (wpsimp simp: obj_at_def)
  apply (rename_tac sc)
  apply (case_tac sc
         ; clarsimp; (solves \<open>corressimp corres: corres_False simp: obj_at_def is_sc_obj_def\<close>)?)

  apply (rename_tac sc n)
  apply (rule_tac F="sc_relation sc n sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
   apply (drule_tac x=sc_ptr in bspec, blast)
   apply (clarsimp simp: sc_relation_def vs_all_heap_simps active_sc_at'_def obj_at'_def projectKOs
                         active_sc_def)

  apply (rule_tac F="scRefills sc' \<noteq> []" in corres_req)
   apply (clarsimp simp: pred_conj_def)
   apply (frule (1) sc_ko_at_valid_objs_valid_sc')
   apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)

  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated)
       apply (rule maybeAddEmptyTail_corres)
      apply (rule_tac f="\<lambda>sc. sc\<lparr>sc_refill_max := max_refills,
                                 sc_refills := [\<lparr>r_time = curTime, r_amount = budget\<rparr>]\<rparr>"
                  and f'="\<lambda>sc'. scRefills_update (\<lambda>_. replaceAt 0 (scRefills sc') (Refill curTime budget))
                                 (scRefillMax_update (\<lambda>_. max_refills)
                                  (scRefillCount_update (\<lambda>_. Suc 0)
                                   (scRefillHead_update (\<lambda>_. 0) sc')))"
                   in setSchedContext_no_stack_update_corres)
         apply clarsimp
         apply (clarsimp simp: sc_relation_def)
         apply (clarsimp simp: refills_map_def wrap_slice_def replaceAt_def refill_map_def null_def)
        apply fastforce
       apply (clarsimp simp: objBits_simps scBits_simps)
      apply fastforce
     apply wpsimp
     apply (wpsimp wp: set_object_wp)
    apply (wpsimp wp: hoare_vcg_conj_lift)
     apply (wpsimp wp: set_sc'.set_wp)
    apply (wpsimp wp: set_sc_valid_objs')
   apply (clarsimp simp: vs_all_heap_simps)
   apply (fastforce dest!: valid_objs_ko_at
                     simp: obj_at_def sc_at_pred_n_def active_sc_def valid_obj_def is_sc_obj_def
                           valid_sched_context_def)
  apply clarsimp
  apply (intro conjI impI allI)
    apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKOs objBitsKO_def scBits_simps)
    apply (intro conjI impI allI)
      apply (metis length_replaceAt list.size(3) list_exhaust_size_eq0)
     apply (clarsimp simp: valid_refills_number'_def obj_at'_def projectKOs objBits_simps'
                           ko_wp_at'_def)
     apply (rule le_trans, simp)
     apply (fastforce simp: scBits_inverse_sc)
    apply (clarsimp simp: ko_wp_at'_def valid_refills_number'_def obj_at'_def projectKOs
                          objBits_simps)
    apply (fastforce simp: scBits_inverse_sc)
   apply (frule (1) sc_ko_at_valid_objs_valid_sc')
   apply (clarsimp simp: valid_sched_context'_def)
   apply (clarsimp simp: valid_refills_number'_def obj_at'_def projectKOs objBits_simps'
                         ko_wp_at'_def)
   apply (rule le_trans, simp)
   apply (fastforce simp: scBits_inverse_sc)
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context_size'_def objBits_simps scBits_simps)
  done

lemma refill_update_bundled:
  "refill_update sc_ptr period budget max_refills
   = (do sc \<leftarrow> get_sched_context sc_ptr;
         head \<leftarrow> return (refill_hd sc);
         update_sched_context sc_ptr (\<lambda>sc. sc\<lparr>sc_refill_max := max_refills,
                                              sc_refills := [head]\<rparr>);
         set_sc_obj_ref sc_period_update sc_ptr period;
         set_sc_obj_ref sc_budget_update sc_ptr budget;
         ready \<leftarrow> get_sc_refill_ready sc_ptr;
         when ready $ do cur_time \<leftarrow> gets cur_time;
                         update_refill_hd sc_ptr (r_time_update (\<lambda>_. cur_time))
                      od;
         sc \<leftarrow> get_sched_context sc_ptr;
         refill_hd \<leftarrow> return (refill_hd sc);
         if budget \<le> r_amount refill_hd
            then do update_refill_hd sc_ptr (r_amount_update (\<lambda>_. budget));
                    maybe_add_empty_tail sc_ptr
                 od
            else do unused \<leftarrow> return $ budget - r_amount refill_hd;
                    new \<leftarrow> return \<lparr>r_time = r_time refill_hd + period, r_amount = unused\<rparr>;
                    refill_add_tail sc_ptr new
                 od
      od)"
  apply (rule monadic_rewrite_to_eq)
  apply (clarsimp simp: refill_update_def)
  apply (simp flip: bind_assoc)
  apply (rule monadic_rewrite_bind_head)+
  apply (rule monadic_rewrite_bind_tail)
  apply (clarsimp simp: monadic_rewrite_def set_refills_def)
  apply (simp add: update_sched_context_decompose_ext2
                       [where f=sc_refills_update and g=sc_refill_max_update]
                   bind_assoc)
  apply wpsimp
  done

lemma refillUpdate_bundled:
  "monadic_rewrite False True (sc_at' scPtr)
     (refillUpdate scPtr newPeriod newBudget newMaxRefills)
     (do sc \<leftarrow> getSchedContext scPtr;
         do sca \<leftarrow> getSchedContext scPtr;
            setSchedContext scPtr
             (scRefills_update (\<lambda>_. replaceAt 0 (scRefills sca) (refillHd sc))
              (scRefillMax_update (\<lambda>_. newMaxRefills)
               (scRefillCount_update (\<lambda>_. 1)
                (scRefillHead_update (\<lambda>_. 0) sca))))
         od;
         sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (scPeriod_update (\<lambda>_. newPeriod) sc);
         sc \<leftarrow> getSchedContext scPtr;
         setSchedContext scPtr (scBudget_update (\<lambda>_. newBudget) sc);
         whenM (refillReady scPtr) $ do curTime \<leftarrow> getCurTime;
                                        updateRefillHd scPtr (rTime_update (\<lambda>_. curTime))
                                     od;
         head \<leftarrow> liftM refillHd $ getSchedContext scPtr;
         if newBudget \<le> rAmount head then do updateRefillHd scPtr (rAmount_update (\<lambda>_. newBudget));
                                             maybeAddEmptyTail scPtr
                                          od
         else do unused \<leftarrow> return (newBudget - rAmount head);
                 new \<leftarrow> return ( Refill_ \<lparr> rTime= rTime head + newPeriod, rAmount= unused \<rparr>);
                 refillAddTail scPtr new
        od
      od)"
  apply (clarsimp simp: refillUpdate_def setRefillIndex_def)
  apply (simp flip: bind_assoc)
  apply (rule monadic_rewrite_bind_head)+
  apply (simp add: bind_assoc)
  apply (rule monadic_rewrite_bind_tail[rotated, OF get_sc_inv'])
  apply (subst bind_assoc_group4)
  apply (rule monadic_rewrite_rewrite_head)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose_decompose_ext2[unfolded K_bind_def])
   apply (clarsimp simp: objBits_simps)
  apply (simp only: bind_assoc)
  apply (subst bind_assoc_group4)
  apply (rule monadic_rewrite_rewrite_head)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose_decompose_ext2[unfolded K_bind_def])
   apply (clarsimp simp: objBits_simps)
  apply (simp only: bind_assoc)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans_dup)
    apply (rule monadic_rewrite_sym)
    apply (rule getSchedContext_setSchedContext_decompose[unfolded K_bind_def])
   apply (rule monadic_rewrite_refl3)
   apply clarsimp
  apply (fastforce simp: objBits_simps length_replaceAt)
  done

lemma refillUpdate_corres:
  "1 < max_refills
   \<Longrightarrow> corres dc
              ((valid_objs and pspace_aligned and pspace_distinct and is_active_sc sc_ptr
                and sc_at sc_ptr) and active_sc_valid_refills)
              (\<lambda>s'. \<exists>n. sc_at'_n n sc_ptr s' \<and> valid_refills_number' max_refills n \<and> valid_objs' s')
              (refill_update sc_ptr period budget max_refills )
              (refillUpdate sc_ptr period budget max_refills)"
  (is "_ \<Longrightarrow> corres _ (?pred and _) ?conc _ _")
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (rule_tac Q="active_sc_at' sc_ptr" in corres_cross_add_guard)
   apply (rule active_sc_at'_cross, simp+)
  apply (subst refill_update_bundled)
  apply (rule monadic_rewrite_corres'
               [where P'=P' and Q=P' for P', simplified pred_conj_def, simplified, rotated])
   apply (rule monadic_rewrite_imp)
    apply (rule refillUpdate_bundled)
   apply simp

  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (rename_tac sc')
  apply clarsimp
  apply (subst update_sched_context_def)
  apply (clarsimp simp: bind_assoc)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rename_tac sc'')
  apply (rule_tac F="sc'' = sc'" in corres_req)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: pred_conj_def cong: conj_cong)
  apply (rule corres_symb_exec_l[OF _ _ get_object_sp, rotated]; (solves wpsimp)?)
    apply (fastforce intro: get_object_exs_valid simp: obj_at_def)
   apply (wpsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj
         ; clarsimp; (solves \<open>corressimp corres: corres_False simp: obj_at_def is_sc_obj_def\<close>)?)
  apply (rename_tac abs_sc abs_n)
  apply (rule_tac F="abs_sc = sc" in corres_req)
   apply (clarsimp simp: obj_at_def)
  apply clarsimp
  apply (rule_tac Q="sc_obj_at (objBits sc' - minSchedContextBits) sc_ptr"
               in corres_cross_add_abs_guard)
   apply (fastforce dest!: state_relationD ko_at'_cross)

  apply (rule_tac Q="\<lambda>_. ?pred and sc_refills_sc_at (\<lambda>refills. length refills = 1) sc_ptr"
              and Q'="\<lambda>_. ?conc and sc_at' sc_ptr
                          and obj_at' (\<lambda>sc. scRefillHead sc = 0 \<and> scRefillCount sc = 1
                                            \<and> scRefillMax sc = max_refills) sc_ptr"
               in corres_split'[rotated 2])
     apply ((wpsimp wp: update_sched_context_valid_objs_update | wpsimp wp: set_object_wp)+)[1]
     apply (fastforce dest!: active_sc_valid_refillsE
                       simp: valid_refills_def vs_all_heap_simps rr_valid_refills_def
                             valid_obj_def valid_sched_context_def active_sc_def sc_at_pred_n_def
                             obj_at_def is_sc_obj_def)
    apply ((wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift | wpsimp wp: set_sc'.set_wp)+)[1]
    apply (frule (1) sc_ko_at_valid_objs_valid_sc')
    apply (fastforce simp: valid_sched_context'_def valid_refills_number'_def obj_at'_def ko_wp_at'_def
                           valid_sched_context_size'_def projectKOs objBits_simps' scBits_inverse_sc)

   apply (rule corres_assume_pre)
   apply (rule corres_guard_imp)
     apply (rule_tac f="\<lambda>sc. sc\<lparr>sc_refill_max := max_refills, sc_refills := [refill_hd sc]\<rparr>"
                 and f'="\<lambda>sc'. scRefills_update (\<lambda>_. replaceAt 0 (scRefills sc') (refillHd sc'))
                                (scRefillMax_update (\<lambda>_. max_refills)
                                 (scRefillCount_update (\<lambda>_. Suc 0)
                                  (scRefillHead_update (\<lambda>_. 0) sc')))"
                  in setSchedContext_no_stack_update_corres)
        apply (clarsimp simp: sc_relation_def)
        apply (prop_tac "max_refills \<le> length (replaceAt 0 (scRefills sc') (refillHd sc'))")
         apply (clarsimp simp: valid_refills_number'_def obj_at'_def projectKOs objBitsKO_def
                               ko_wp_at'_def scBits_simps)
        apply (prop_tac "0 < scRefillCount sc' \<and> scRefillHead sc' < scRefillMax sc'
                         \<and> scRefillMax sc' \<le> length (scRefills sc') \<and> 0 < length (scRefills sc')")
         apply (prop_tac "sc_relation sc n sc'")
          apply (fastforce simp: sc_relation_def)
         apply (frule (1) sc_ko_at_valid_objs_valid_sc')
         apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                          simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
        apply (clarsimp simp: refills_map_def)
        apply (rule nth_equalityI; clarsimp)
        apply (subst hd_conv_nth)
         apply (rule length_greater_0_conv[THEN iffD1])
         apply (subst length_map)
         apply (subst length_wrap_slice; simp)
        apply (subst nth_map)
         apply (subst length_wrap_slice; simp)
        apply (subst wrap_slice_index; simp)+
        apply (subst replaceAt_index; fastforce simp: refillHd_def)
       apply fastforce
      apply (fastforce simp: objBits_simps)
     apply simp
    apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: obj_at'_def)

  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>_. ?pred and sc_refills_sc_at (\<lambda>refills. length refills = 1) sc_ptr"
              and Q'="\<lambda>_. ?conc and sc_at' sc_ptr
                          and obj_at' (\<lambda>sc. scRefillHead sc = 0 \<and> scRefillCount sc = 1
                                            \<and> scRefillMax sc = max_refills) sc_ptr"
               in corres_split'[rotated 2])
     apply ((wpsimp wp: update_sched_context_valid_objs_update
             | wpsimp wp: update_sched_context_wp)+)[1]
     apply (fastforce dest!: valid_objs_ko_at
                       simp: valid_obj_def valid_sched_context_def obj_at_def is_sc_obj_def
                             sc_at_pred_n_def)
    apply ((wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift | wpsimp wp: set_sc'.set_wp)+)[1]
    apply (frule (1) sc_ko_at_valid_objs_valid_sc')
    apply (fastforce simp: valid_sched_context'_def ps_clear_def valid_refills_number'_def
                           obj_at'_def projectKOs objBits_simps' valid_sched_context_size'_def)
   apply (corressimp corres: update_sc_no_reply_stack_update_ko_at'_corres
                               [where f'="scPeriod_update (\<lambda>_. period)"]
                       simp: sc_relation_def objBits_simps)

  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>_. ?pred and sc_refills_sc_at (\<lambda>refills. length refills = 1) sc_ptr"
              and Q'="\<lambda>_. ?conc and sc_at' sc_ptr
                          and obj_at' (\<lambda>sc. scRefillHead sc = 0 \<and> scRefillCount sc = 1
                                            \<and> scRefillMax sc = max_refills) sc_ptr"
               in corres_split'[rotated 2])
     apply ((wpsimp wp: update_sched_context_valid_objs_update
             | wpsimp wp: update_sched_context_wp)+)[1]
     apply (fastforce dest!: valid_objs_ko_at
                       simp: valid_obj_def valid_sched_context_def obj_at_def is_sc_obj_def
                             sc_at_pred_n_def)
    apply ((wpsimp wp: hoare_vcg_ex_lift hoare_vcg_conj_lift | wpsimp wp: set_sc'.set_wp)+)[1]
    apply (frule (1) sc_ko_at_valid_objs_valid_sc')
    apply (fastforce simp: valid_sched_context'_def length_replaceAt valid_refills_number'_def
                          obj_at'_def projectKOs objBits_simps' ko_wp_at'_def scBits_inverse_sc
                          valid_sched_context_size'_def ps_clear_def)
   apply (corressimp corres: update_sc_no_reply_stack_update_ko_at'_corres
                               [where f'="scBudget_update (\<lambda>_. budget)"]
                       simp: sc_relation_def objBits_simps)

  apply (clarsimp simp: whenM_def ifM_def bind_assoc when_def getRefillNext_getSchedContext
                        getRefillSize_def2 liftM_def)
  apply (rule corres_split'[rotated 2, OF get_sc_refill_ready_inv refillReady_inv])
   apply (corressimp corres: refillReady_corres)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply (rule_tac Q="\<lambda>_. ?pred and sc_refills_sc_at (\<lambda>refills. length refills = 1) sc_ptr"
              and Q'="\<lambda>_. valid_objs' and obj_at' (\<lambda>sc. scRefillHead sc = 0 \<and> scRefillCount sc = 1
                                                         \<and> scRefillMax sc = max_refills) sc_ptr"
              and r'=dc
               in corres_split'[rotated 2])
     apply (simp add: update_refill_hd_def set_refills_def)
     apply ((wpsimp wp: update_sched_context_valid_objs_update get_refills_wp
             | wpsimp wp: update_sched_context_wp get_refills_wp)+)[1]
     apply (intro conjI impI allI)
      apply (clarsimp simp: valid_sched_context_def)
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
    apply ((wpsimp simp: updateRefillHd_def
                     wp: set_sc'.valid_objs'
            | wpsimp wp: set_sc'.set_wp)+)[1]
    apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                           valid_obj'_def length_replaceAt
                           obj_at'_def projectKOs ps_clear_def)
   apply (corressimp corres: getCurTime_corres updateRefillHd_corres
                       simp: refill_map_def obj_at_kh_kheap_simps vs_all_heap_simps)
   apply fastforce

  apply clarsimp
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
  apply (rename_tac abs_sc conc_sc)
  apply (rule_tac F="0 < scRefillCount conc_sc \<and> scRefillCount conc_sc \<le> scRefillMax conc_sc
                     \<and> scRefillHead conc_sc < scRefillMax conc_sc
                     \<and> scRefillMax conc_sc \<le> length (scRefills conc_sc)
                     \<and> length (sc_refills abs_sc) = 1"
               in corres_req)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: valid_sched_context'_def sc_relation_def sc_at_pred_n_def obj_at_def
                          refills_map_def)
  apply (clarsimp split del: if_split)
  apply (frule_tac sc=abs_sc and sc'=conc_sc in refill_hd_relation; (solves simp)?)
  apply (clarsimp simp: refill_map_def)
  apply (intro conjI impI allI)
   apply (rule corres_guard_imp)
     apply (rule corres_split_deprecated[OF _ updateRefillHd_corres])
         apply (rule maybeAddEmptyTail_corres)
        apply simp
       apply (clarsimp simp: refill_map_def)
      apply (simp add: update_refill_hd_def set_refills_def)
      apply ((wpsimp wp: update_sched_context_valid_objs_update get_refills_wp
              | wpsimp wp: update_sched_context_wp get_refills_wp)+)[1]
     apply (clarsimp simp: updateRefillHd_def)
     apply (rule hoare_vcg_conj_lift
            , (wpsimp wp: set_sc'.valid_objs'
               | wpsimp wp: set_sc'.set_wp)+)[1]
    apply (fastforce simp: obj_at_def active_sc_def vs_all_heap_simps sc_at_pred_n_def
                           valid_sched_context_def)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: updateRefillHd_def valid_obj'_def valid_sched_context'_def
                          valid_sched_context_size'_def length_replaceAt objBits_simps
                          obj_at'_def projectKOs length_ineq_not_Nil(2))
  apply (corressimp corres: refillAddTail_corres
                      simp: obj_at'_def projectKOs refill_map_def obj_at_def is_sc_obj_def)
  done

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma invoke_sched_control_configure_corres:
  "sc_ctrl_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres (=)
          (einvs and valid_sched_control_inv sc_inv and simple_sched_action and ct_active)
          (invs' and sch_act_simple and valid_sc_ctrl_inv' sc_inv' and ct_active')
          (invoke_sched_control_configure sc_inv)
          (invokeSchedControlConfigure sc_inv')"
  apply (cases sc_inv)
  apply (simp add: invoke_sched_control_configure_def invokeSchedControlConfigure_def)
  sorry

end

end
