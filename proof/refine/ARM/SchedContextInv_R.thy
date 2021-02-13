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
