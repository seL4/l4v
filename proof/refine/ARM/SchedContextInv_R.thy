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

lemma getCurTime_sp:
  "\<lbrace>P\<rbrace> getCurTime \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurTime s)\<rbrace>"
  by (wpsimp simp: getCurTime_def)

lemma isRoundRobin_corres:
  "corres (=) (sc_at sc_ptr) (sc_at' sc_ptr)
              (is_round_robin sc_ptr) (isRoundRobin sc_ptr)"
  apply (clarsimp simp: is_round_robin_def isRoundRobin_def)
  apply (corressimp corres: get_sc_corres
                      simp: sc_relation_def)
  done

lemma valid_obj'_scPeriod_update[simp]:
  "valid_obj' (KOSchedContext (scPeriod_update (\<lambda>_. period) sc')) = valid_obj' (KOSchedContext sc')"
  by (fastforce simp: valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def objBits_simps)

(* it would be good to rewrite all getting wp rules in this form *)
lemma getSchedContext_wp':
  "\<lbrace>\<lambda>s. sc_at' p s  \<longrightarrow> P (the (scs_of' s p)) s\<rbrace> getSchedContext p \<lbrace>P\<rbrace>"
  by (wpsimp simp: obj_at'_def projectKOs opt_map_left_Some)

lemma ovalid_readRefillReady'[rule_format, simp]:
  "ovalid (\<lambda>s. sc_at' scp s \<longrightarrow> P (((\<lambda>sc'. rTime (refillHd sc') \<le> ksCurTime s + kernelWCETTicks) |< scs_of' s) scp) s)
              (readRefillReady scp) P"
  unfolding readRefillReady_def readSchedContext_def ovalid_def
  by (fastforce simp: obind_def opt_map_left_Some obj_at'_def projectKOs
                dest: use_ovalid[OF ovalid_readCurTime]
               dest!: readObject_misc_ko_at'
               split: option.split_asm)+

lemma refillReady_wp':
  "\<lbrace>\<lambda>s. sc_at' scp s \<longrightarrow>
        P (((\<lambda>sc'. rTime (refillHd sc') \<le> ksCurTime s + kernelWCETTicks) |< scs_of' s) scp) s\<rbrace>
    refillReady scp \<lbrace>P\<rbrace>"
  unfolding refillReady_def
  by wpsimp (drule use_ovalid[OF ovalid_readRefillReady'])

lemma refillAddTail_corres:
  "time = time' \<and> amount = amount'
   \<Longrightarrow> corres dc (sc_at sc_ptr)
                 (sc_at' sc_ptr and
                  (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr))
                 (refill_add_tail sc_ptr \<lparr>r_time = time, r_amount = amount\<rparr>)
                 (refillAddTail sc_ptr (Refill time' amount'))"
  supply projection_rewrites[simp]
  apply (clarsimp simp: refill_add_tail_def refillAddTail_def getRefillNext_getSchedContext
                        getRefillSize_def2 liftM_def get_refills_def)
  apply (rule corres_symb_exec_r[OF _ get_sc_sp', rotated]; (solves wpsimp)?)+
  apply (rename_tac sc')
  apply (rule corres_guard_imp)
    apply (rule corres_assert_assume_r)
    apply (rule updateSchedContext_corres_gen[where P=\<top>
                and P'="(\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr)"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (clarsimp simp: obj_at_simps is_sc_obj)
      apply (rename_tac sc')
      apply (clarsimp simp: sc_relation_def neq_Nil_lengthI opt_map_left_Some)
      apply (prop_tac "scRefills sc' \<noteq> []")
       apply (clarsimp simp: neq_Nil_lengthI)
      apply (clarsimp simp: refills_map_def)
      apply (subst wrap_slice_append; simp)
      apply (insert less_linear)[1]
      apply (drule_tac x="scRefillMax sc'" and y="scRefillHead sc' + scRefillCount sc' + Suc 0" in meta_spec2)
      apply (erule disjE)
       apply (simp add: refillNextIndex_def refillTailIndex_def Let_def)
       apply (intro conjI impI;
              clarsimp simp: Suc_diff_Suc wrap_slice_updateAt_eq[symmetric] neq_Nil_lengthI
                             nat_le_Suc_less refill_map_def updateAt_index)
      apply (erule disjE)
       apply clarsimp
       apply (rule conjI)
        apply (simp add: refillNextIndex_def refillTailIndex_def Let_def)
        apply (clarsimp simp: wrap_slice_updateAt_eq not_le)
        apply (metis add_leE le_SucI le_refl lessI mult_is_add.mult_commute not_add_less2 not_less_eq wrap_slice_updateAt_eq)
       apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def not_le)
       apply (clarsimp simp: updateAt_index refill_map_def)
      apply clarsimp
      apply (rule conjI)
       apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def)
       apply (intro conjI impI; (clarsimp simp: not_le wrap_slice_updateAt_eq)?)
       apply (metis add_leE le_refl le_simps(1) less_SucI mult_is_add.mult_commute nat_neq_iff
                    not_less_eq trans_less_add2 wrap_slice_updateAt_eq)
      apply (clarsimp simp: refillNextIndex_def refillTailIndex_def Let_def not_le)
      apply (clarsimp simp: updateAt_index refill_map_def)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                     dest!: state_relation_sc_replies_relation_sc)
    apply (clarsimp simp: objBits_simps)
   apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (clarsimp simp: obj_at'_def projectKOs opt_map_left_Some)
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
          (is_active_sc2 sc_ptr)
                 (sc_at' sc_ptr and
                  (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' < scRefillMax sc' \<and> sc_valid_refills' sc') |< scs_of' s') sc_ptr))
          (maybe_add_empty_tail sc_ptr)
          (maybeAddEmptyTail sc_ptr)" (is "corres _ ?abs ?conc _ _")
  supply projection_rewrites[simp]
  apply (rule corres_cross_add_abs_guard[where Q="sc_at sc_ptr"])
   apply (fastforce dest!: sc_at'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: maybe_add_empty_tail_def maybeAddEmptyTail_def get_refills_def)
  apply (rule corres_split'[rotated 2, OF is_round_robin_sp isRoundRobin_sp])
   apply (corressimp corres: isRoundRobin_corres)
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (clarsimp simp: when_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (corressimp corres: get_sc_corres)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: obj_at_def is_sc_obj_def)
  apply (rename_tac sc')
  apply (corressimp corres: refillAddTail_corres)
  apply (frule refill_hd_relation; clarsimp simp: obj_at'_def projectKOs opt_map_left_Some)
  apply (fastforce dest: valid_objs_valid_sched_context_size
                   simp: obj_at_def is_sc_obj_def refill_map_def)
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

lemma sc_relation_updateRefillHd:
  "\<lbrakk>sc_relation sc n sc'; \<forall>refill'. f (refill_map refill') = refill_map (f' refill');
        sc_valid_refills' sc'\<rbrakk>
       \<Longrightarrow> sc_relation (sc_refills_update (\<lambda>refills. f (hd refills) # tl refills) sc) n
            (scRefills_update (\<lambda>_. updateAt (scRefillHead sc') (scRefills sc') f') sc')"
  apply (prop_tac "wrap_slice (scRefillHead sc') (scRefillCount sc') (scRefillMax sc') (scRefills sc') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI)
  apply (clarsimp simp: sc_relation_def refills_map_def tl_map hd_map)
  apply (subst hd_Cons_tl[where xs="wrap_slice _ _ _ (updateAt _ _ _)", symmetric])
   apply (clarsimp intro!: neq_Nil_lengthI)
  apply simp
  apply (subst hd_wrap_slice; (simp add: updateAt_index tl_wrap_slice neq_Nil_lengthI)?)+
  apply (case_tac "Suc (scRefillHead sc') < scRefillMax sc'")
   apply (prop_tac "wrap_slice (Suc (scRefillHead sc')) (scRefillCount sc' - Suc 0)
                 (scRefillMax sc') (updateAt (scRefillHead sc') (scRefills sc') f')
          = wrap_slice (Suc (scRefillHead sc')) (scRefillCount sc' - Suc 0) (scRefillMax sc') (scRefills sc')")
    apply (subst wrap_slice_updateAt_eq[symmetric]; clarsimp)
     apply (fastforce simp: neq_Nil_lengthI)+
  apply (clarsimp simp: not_less le_eq_less_or_eq[where m="scRefillMax sc'" for sc'])
  done

lemma updateRefillHd_corres:
  "\<lbrakk>sc_ptr = scPtr; \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = (refill_map (f' refill'))\<rbrakk>
   \<Longrightarrow> corres dc
        (sc_at sc_ptr and is_active_sc2 sc_ptr)
        (valid_refills' sc_ptr and sc_at' sc_ptr)
        (update_refill_hd sc_ptr f)
        (updateRefillHd scPtr f')"
  supply projection_rewrites[simp]
  apply (rule_tac Q="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce dest!: is_active_sc'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: update_refill_hd_def updateRefillHd_def)
  apply (rule corres_guard_imp)
    apply (rule updateSchedContext_corres_gen[where P=\<top>
      and P'="valid_refills' sc_ptr and is_active_sc' scPtr"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (fastforce simp: is_sc_obj obj_at_simps is_active_sc'_def opt_map_left_Some valid_refills'_def
                      elim!: sc_relation_updateRefillHd)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                     dest!: state_relation_sc_replies_relation_sc)
  by (clarsimp simp: objBits_simps)+

lemma sc_relation_updateRefillTl:
  "\<lbrakk> sc_relation sc n sc'; \<forall>refill'. f (refill_map refill') = refill_map (f' refill');
        sc_valid_refills' sc'\<rbrakk>
       \<Longrightarrow> sc_relation
            (sc_refills_update (\<lambda>refills. butlast refills @ [f (last refills)]) sc) n
            (scRefills_update (\<lambda>_. updateAt (refillTailIndex sc') (scRefills sc') f') sc')"
  apply (prop_tac "scRefills sc' \<noteq> []")
   apply fastforce
  apply (clarsimp simp: sc_relation_def refills_map_def)
  apply (simp add: snoc_eq_iff_butlast)
  apply (prop_tac "wrap_slice (scRefillHead sc') (scRefillCount sc') (scRefillMax sc')
              (scRefills sc') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI)
  apply (prop_tac "wrap_slice (scRefillHead sc') (scRefillCount sc') (scRefillMax sc')
              (updateAt (refillTailIndex sc') (scRefills sc') f') \<noteq> []")
   apply (clarsimp intro!: neq_Nil_lengthI)
  apply clarsimp
  apply (prop_tac "wrap_slice (scRefillHead sc') (scRefillCount sc' - Suc 0)
             (scRefillMax sc')
             (updateAt (refillTailIndex sc') (scRefills sc') f') = wrap_slice (scRefillHead sc') (scRefillCount sc' - Suc 0)
             (scRefillMax sc')
             (scRefills sc')")
   apply (subst wrap_slice_updateAt_eq[symmetric]; (simp add: refillTailIndex_def Let_def split: if_split_asm)?)
   apply (intro conjI impI; linarith)
  apply (clarsimp simp: butlast_map butlast_wrap_slice)
  apply (clarsimp simp: last_map)
  apply (subst last_wrap_slice; simp?)+
  apply (intro conjI impI)
   apply (subst updateAt_index; simp add: refillTailIndex_def)+
  done

lemma updateRefillTl_corres:
  "\<lbrakk>sc_ptr = scPtr;
    \<forall>refill refill'. refill = refill_map refill' \<longrightarrow> f refill = (refill_map (f' refill'))\<rbrakk>
   \<Longrightarrow> corres dc
              (sc_at sc_ptr and is_active_sc2 sc_ptr)
              (sc_at' scPtr and valid_objs')
              (update_refill_tl sc_ptr f)
              (updateRefillTl scPtr f')"
  supply projection_rewrites[simp]
  apply (rule_tac Q="is_active_sc' scPtr" in corres_cross_add_guard)
   apply (fastforce dest!: is_active_sc'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: update_refill_tl_def updateRefillTl_def)
  apply (rule corres_guard_imp)
    apply (rule updateSchedContext_corres_gen[where P=\<top> and P'="valid_objs' and is_active_sc' scPtr"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (clarsimp simp: is_sc_obj obj_at_simps is_active_sc'_def)
      apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def valid_sched_context'_def)
      apply (clarsimp simp: sc_relation_updateRefillTl opt_map_left_Some)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                     dest!: state_relation_sc_replies_relation_sc)
  by (clarsimp simp: objBits_simps)+

lemma getCurSc_sp:
  "\<lbrace>P\<rbrace>
   getCurSc
   \<lbrace>\<lambda>rv s. P s \<and> rv = ksCurSc s\<rbrace>"
  apply (simp add: getCurSc_def)
  apply (wpsimp wp: hoare_return_sp)
  done

lemma refillBudgetCheckRoundRobin_corres:
  "corres dc
          (cur_sc_active and (\<lambda>s. sc_at (cur_sc s) s))
          (valid_objs' and (\<lambda>s'. sc_at' (ksCurSc s') s'))
          (refill_budget_check_round_robin usage) (refillBudgetCheckRoundRobin usage)"
  supply projection_rewrites[simp]
  apply (subst is_active_sc_rewrite)
  apply (clarsimp simp: refill_budget_check_round_robin_def refillBudgetCheckRoundRobin_def)
  apply (rule corres_split'[rotated 2, OF gets_sp getCurSc_sp])
   apply (corressimp corres: getCurSc_corres)
  apply (rule_tac Q="\<lambda>s. is_active_sc' (ksCurSc s) s" in corres_cross_add_guard)
   apply (rule_tac ptr="ksCurSc s'" in is_active_sc'_cross[OF state_relation_pspace_relation]; simp)
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF updateRefillHd_corres], simp)
       apply (clarsimp simp: refill_map_def)
      apply (rule updateRefillTl_corres, simp)
      apply (clarsimp simp: refill_map_def)
     apply (wpsimp simp: update_refill_hd_rewrite wp: set_refills_wp get_refills_wp)
    apply (wpsimp wp: hoare_vcg_conj_lift)
     apply (wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)
    apply (wpsimp wp: updateRefillHd_valid_objs')
   apply (clarsimp simp: obj_at_def is_active_sc2_def is_sc_obj opt_map_left_Some
                  split: option.split_asm Structures_A.kernel_object.split_asm)
  apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] scBits_simps ps_clear_upd)
  apply (erule (1) valid_objsE')
  apply (clarsimp simp: is_active_sc'_def valid_obj'_def valid_sched_context'_def valid_refills'_def
                 split: option.split_asm)
  done

lemmas sc_relation_refillResetRR1 =
  sc_relation_updateRefillTl[where f="r_amount_update (\<lambda>_. 0)" and f'="rAmount_update (\<lambda>_. 0)"]

lemma sc_relation_refillResetRR2:
  "\<lbrakk>sc_relation sc n sc'; length (sc_refills sc) = 2; sc_refill_max sc = MIN_REFILLS;
    sc_valid_refills' sc'; 1 < scRefillCount sc'\<rbrakk>
    \<Longrightarrow> sc_relation
             (sc_refills_update
               (\<lambda>refills. r_amount_update (\<lambda>m. m + r_amount (hd (tl refills))) (hd refills) # tl refills)
               sc)
             n ((scRefills_update
                         (\<lambda>_. updateAt (scRefillHead sc') (scRefills sc')
                                (\<lambda>hd. rAmount_update (\<lambda>_. rAmount hd + rAmount (refillTl sc')) hd)))
                 sc')"
  apply (case_tac "sc_refills sc"; simp)
  apply (rename_tac ls; case_tac ls; clarsimp simp: MIN_REFILLS_def)
  apply (cases sc; simp add: sc_relation_def refills_map_def)
  apply (prop_tac "scRefillCount sc' = 2")
   apply (insert length_wrap_slice[of "scRefillCount sc'" "scRefillMax sc'" "scRefillHead sc'" "scRefills sc'"])
   apply (case_tac "scRefillHead sc'"; simp)
  apply (clarsimp simp: refill_map_def updateAt_def Let_def null_def)
  apply (clarsimp simp: wrap_slice_def)
  apply (intro conjI; clarsimp simp: updateAt_def Let_def null_def refill_map_def)
   apply (case_tac "scRefills sc'"; simp)
   apply (rename_tac list; case_tac list; simp add: refill_map_def refillTl_def refillTailIndex_def)
  apply (case_tac "scRefillHead sc'"; simp)
  apply (intro conjI; clarsimp)
  apply (case_tac "scRefills sc'"; simp)
  apply (rename_tac list; case_tac list; simp add: refill_map_def refillTl_def refillTailIndex_def)
  done

lemma sc_relation_refillResetRR:
  "\<lbrakk>sc_relation sc n sc'; length (sc_refills sc) = 2; sc_refill_max sc = MIN_REFILLS;
    sc_valid_refills' sc'; 1 < scRefillCount sc'\<rbrakk>
   \<Longrightarrow> sc_relation
             (sc_refills_update
               ((\<lambda>refills. butlast refills @ [last refills\<lparr>r_amount := 0\<rparr>]) \<circ>
                (\<lambda>refills. r_amount_update (\<lambda>m. m + r_amount (hd (tl refills))) (hd refills) # tl refills))
               sc)
             n (((\<lambda>sc. scRefills_update (\<lambda>_. updateAt (refillTailIndex sc) (scRefills sc) (rAmount_update (\<lambda>_. 0)))
                         sc) \<circ>
                 (\<lambda>sc. scRefills_update
                         (\<lambda>_. updateAt (scRefillHead sc) (scRefills sc)
                                (\<lambda>hd. rAmount_update (\<lambda>_. rAmount hd + rAmount (refillTl sc)) hd))
                         sc))
                 sc')"
  apply (drule sc_relation_refillResetRR2; fastforce?)
  by (drule sc_relation_refillResetRR1; clarsimp simp: refill_map_def)

lemma refillResetRR_corres:
  "corres dc (sc_at csc_ptr and is_active_sc csc_ptr
                  and round_robin csc_ptr and valid_refills csc_ptr)
             (valid_objs' and sc_at' csc_ptr)
             (refill_reset_rr csc_ptr) (refillResetRR csc_ptr)"
  (is "corres dc ?abs ?conc _ _")
  supply projection_rewrites[simp]
  apply (subst is_active_sc_rewrite)
  apply (subst valid_refills_rewrite)
  apply (rule_tac Q="is_active_sc' csc_ptr" in corres_cross_add_guard)
   apply (fastforce dest!: is_active_sc'_cross[OF state_relation_pspace_relation])
  apply (rule_tac Q="\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' = 2) |< scs_of' s') csc_ptr"
         in corres_cross_add_guard)
   apply (clarsimp simp: obj_at'_def projectKOs round_robin2_def obj_at_def is_sc_obj
                         rr_valid_refills_def is_active_sc2_def is_active_sc'_def opt_map_left_Some)
   apply (drule (1) pspace_relation_absD[where x=csc_ptr, OF _ state_relation_pspace_relation])
   apply (erule (1) valid_objsE')
   apply (clarsimp simp: sc_relation_def refills_map_def valid_sched_context'_def valid_obj'_def)
  apply (clarsimp simp: refill_reset_rr_def refillResetRR_def get_refills_def updateRefillTl_def
                        update_sched_context_decompose[symmetric, simplified] update_refill_tl_def)
  apply (rule corres_guard_imp)
    apply (rule monadic_rewrite_corres'[OF _ monadic_rewrite_sym[OF updateSchedContext_decompose[simplified]]])
    apply (rule updateSchedContext_corres_gen[where
                 P="(\<lambda>s. ((\<lambda>sc. length (sc_refills sc) = 2 \<and> sc_refill_max sc = MIN_REFILLS) |< scs_of2 s) csc_ptr)"
            and P'="valid_objs' and is_active_sc' csc_ptr and (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' = 2) |< scs_of' s') csc_ptr)"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (clarsimp simp: is_sc_obj obj_at_simps is_active_sc'_def opt_map_left_Some)
      apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def valid_sched_context'_def)
      apply (fastforce elim!: sc_relation_refillResetRR[simplified])
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                     dest!: state_relation_sc_replies_relation_sc)
     apply (clarsimp simp: objBits_simps)+
   apply (clarsimp simp: round_robin2_def obj_at_def is_sc_obj rr_valid_refills_def opt_map_left_Some)
  by (clarsimp simp: objBits_simps)

lemma refillPopHead_corres:
  "corres (\<lambda>refill refill'. refill = refill_map refill')
              (pspace_aligned and pspace_distinct and sc_at sc_ptr and is_active_sc sc_ptr
               and sc_refills_sc_at (\<lambda>refills. 1 < length refills) sc_ptr)
              valid_objs'
              (refill_pop_head sc_ptr) (refillPopHead sc_ptr)"
  (is "corres _ ?abs ?conc _ _")
  supply if_split[split del]
  supply projection_rewrites[simp]
  apply (subst is_active_sc_rewrite)
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel], fastforce)
  apply (rule_tac Q="is_active_sc' sc_ptr" in corres_cross_add_guard)
   apply (fastforce dest!: is_active_sc'_cross[OF state_relation_pspace_relation])
  apply (clarsimp simp: refill_pop_head_def refillPopHead_def)
  apply (clarsimp simp: getRefillNext_getSchedContext get_refills_def liftM_def)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (rule corres_guard_imp)
     apply (rule get_sc_corres)
    apply simp
   apply simp
  apply (rename_tac sc')
  apply (rule_tac F="refill_hd sc = refill_map (refillHd sc')" in corres_req)
   apply (clarsimp simp: obj_at_def is_sc_obj obj_at'_def projectKOs)
   apply (frule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
   apply (clarsimp elim!: refill_hd_relation)
   apply (erule (1) valid_objsE')
   apply (clarsimp simp: valid_obj'_def valid_sched_context'_def is_active_sc'_def opt_map_left_Some)
  apply (rule corres_guard_imp)
    apply (rule corres_split'[OF updateSchedContext_corres_gen[where
                                    P="(\<lambda>s. ((\<lambda>sc. 1 < length (sc_refills sc)) |< scs_of2 s) sc_ptr)"
                                and P'="valid_objs' and is_active_sc' sc_ptr"]])
         apply (clarsimp, drule (2) state_relation_sc_relation)
         apply (clarsimp simp: sc_relation_def refills_map_def tl_map obj_at_simps is_sc_obj opt_map_left_Some)
         apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def valid_sched_context'_def)
         apply (subst tl_wrap_slice; clarsimp simp: min_def split: if_split)
         apply (rule conjI impI; clarsimp simp: refillNextIndex_def wrap_slice_start_0 split: if_splits)
        apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                        dest!: state_relation_sc_replies_relation_sc)
        apply clarsimp
       apply (clarsimp simp: objBits_simps)
      apply simp
     apply (wpsimp wp: update_sched_context_wp)
    apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: sc_refills_sc_at_def obj_at_def opt_map_left_Some)
  apply simp
  done

lemma refillNew_corres:
  "\<lbrakk>1 < max_refills; valid_refills_number' max_refills (min_sched_context_bits + n)\<rbrakk>
   \<Longrightarrow> corres dc
         (pspace_aligned and pspace_distinct and sc_obj_at n sc_ptr) \<top>
            (refill_new sc_ptr max_refills budget period)
            (refillNew sc_ptr max_refills budget period)"
  supply projection_rewrites[simp]
  supply getSchedContext_wp[wp del] set_sc'.get_wp[wp del]
  apply (rule corres_cross_add_guard[where
      Q = "sc_at' sc_ptr and (\<lambda>s'. ((\<lambda>sc. objBits sc = minSchedContextBits + n) |< scs_of' s') sc_ptr)"])
   apply (fastforce dest!: sc_obj_at_cross[OF state_relation_pspace_relation]
                     simp: obj_at'_def projectKOs opt_map_left_Some)
  apply (unfold refillNew_def refill_new_def setRefillHd_def updateRefillHd_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ getCurTime_corres])
      (* period *)
      apply (rule corres_split[OF updateSchedContext_corres]; clarsimp simp: objBits_simps)
     apply (fastforce simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some
                     dest!: state_relation_sc_relation)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                     dest!: state_relation_sc_replies_relation_sc)
        (* budget *)
        apply (rule corres_split[OF updateSchedContext_corres]; (clarsimp simp: objBits_simps)?)
     apply (fastforce simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some
                     dest!: state_relation_sc_relation)
           apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                           dest!: state_relation_sc_replies_relation_sc)
          (* max_refills, sc_refills update *)
          (* rewrite into one step updateSchedContext corres *)
          apply (rename_tac ctime)
          apply (rule_tac P="sc_obj_at n sc_ptr and (\<lambda>s. ctime = cur_time s)"
                      and P'="sc_at' sc_ptr and (\<lambda>s'. ctime = ksCurTime s')
                              and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n) |< scs_of' s') sc_ptr)"
                 in corres_inst)
          apply (subst bind_assoc[symmetric])
          apply (subst update_sched_context_decompose[symmetric, simplified])
          apply (subst bind_assoc[symmetric])
          apply (subst bind_assoc[symmetric])
          apply (subst bind_assoc)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF  monadic_rewrite_corres'
                                           [OF _ monadic_rewrite_sym
                                                   [OF updateSchedContext_decompose_x2[simplified]]]])
                  (* use setSchedContext_corres *)
                  apply (rule monadic_rewrite_corres[OF _ update_sched_context_rewrite[where n=n]])
                  apply (simp add: updateSchedContext_def)
                  apply (rule corres_split[OF get_sc_corres])
                    apply (rename_tac sc')
                    apply (rule_tac P="ko_at (kernel_object.SchedContext sc n) sc_ptr"
                                and P'="ko_at' sc' sc_ptr
                                        and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n) |< scs_of' s') sc_ptr)"
                           in corres_inst)
                    apply (rule_tac F="length (scRefills sc') = max_num_refills (min_sched_context_bits + n)"
                           in corres_req)
                     apply (clarsimp simp: obj_at_simps scBits_simps opt_map_left_Some)
                    using scBits_inverse_sc apply fastforce
                    apply (rule stronger_corres_guard_imp)
                      apply (rule_tac sc'="sc'\<lparr> scRefillMax := max_refills,
                                                scRefillHead := 0,
                                                scRefillCount := Suc 0,
                                                scRefills := updateAt 0 (scRefills sc') (\<lambda>r. Refill ctime budget)\<rparr>"
                             in setSchedContext_corres)
                       apply (clarsimp simp: sc_relation_def refills_map_def valid_refills_number'_def
                                             wrap_slice_start_0 max_num_refills_eq_refillAbsoluteMax')
                       apply (case_tac "scRefills sc'"; simp add: updateAt_def null_def refill_map_def)
                      apply (clarsimp simp: objBits_simps scBits_simps)
                     apply simp
                    apply (fastforce simp: obj_at_simps is_sc_obj opt_map_left_Some
                                    dest!: sc_replies_relation_prevs_list[OF state_relation_sc_replies_relation])
                   apply (wpsimp wp: getSchedContext_wp')+
                 apply (clarsimp simp: objBits_simps)+
              (* last step : add tail *)
              apply (rule_tac P="sc_obj_at n sc_ptr and is_active_sc2 sc_ptr"
                          and P'="sc_at' sc_ptr
                                  and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n
                                             \<and> scRefillHead sc' = 0 \<and> scRefillCount sc' = 1
                                             \<and> scRefillMax sc' = max_refills) |< scs_of' s') sc_ptr)"
                     in corres_inst)
              apply (rule stronger_corres_guard_imp)
                apply (rule maybeAddEmptyTail_corres[simplified dc_def])
               apply simp
              apply (clarsimp simp: obj_at_simps is_sc_obj scBits_simps opt_map_left_Some
                                    valid_refills_number'_def)
              apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, rotated])
              using scBits_inverse_sc apply fastforce
             apply (wpsimp wp: update_sched_context_wp updateSchedContext_wp)+
           apply (clarsimp simp:  obj_at_def is_sc_obj is_active_sc2_def)
          apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] valid_objs'_def ps_clear_upd
                                opt_map_left_Some)
         apply (wpsimp wp: update_sched_context_wp updateSchedContext_wp)+
   apply (clarsimp simp:  obj_at_def is_sc_obj is_active_sc2_def)
  apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] valid_objs'_def ps_clear_upd opt_map_left_Some)
  done

lemma refillUpdate_corres:
  "\<lbrakk>1 < max_refills; valid_refills_number' max_refills (min_sched_context_bits + n)\<rbrakk>
   \<Longrightarrow> corres dc
              ((is_active_sc2 sc_ptr and sc_obj_at n sc_ptr) and (pspace_aligned and pspace_distinct))
              (valid_refills' sc_ptr)
              (refill_update sc_ptr period budget max_refills)
              (refillUpdate sc_ptr period budget max_refills)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> corres _ (?pred and _) ?conc _ _")
  supply getSchedContext_wp[wp del] set_sc'.get_wp[wp del] projection_rewrites[simp]
  apply (rule corres_cross_add_guard[where
      Q = "sc_at' sc_ptr and (\<lambda>s'. ((\<lambda>sc. objBits sc = minSchedContextBits + n) |< scs_of' s') sc_ptr)"])
   apply (fastforce dest!: sc_obj_at_cross[OF state_relation_pspace_relation]
                     simp: obj_at'_def projectKOs opt_map_left_Some)
  apply (rule_tac Q="is_active_sc' sc_ptr" in corres_cross_add_guard)
   apply (rule is_active_sc'_cross, fastforce+)
  apply (rule corres_guard_imp)
    apply (rule_tac P="?pred" and P'="?conc and sc_at' sc_ptr" in corres_inst)
    apply (unfold refillUpdate_def refill_update_def)
    apply simp
    (* rewrite the refill list update steps into one step updateSchedContext corres *)
    apply (subst bind_assoc[where m="update_sched_context _ _", symmetric])
    apply (subst update_sched_context_decompose[symmetric, simplified])
    apply (subst bind_assoc[where m="updateSchedContext _ _", symmetric])
    apply (subst bind_assoc[where m="do _ \<leftarrow> updateSchedContext _ _; updateSchedContext _ _ od", symmetric])
    apply (subst bind_assoc[where m="do _ \<leftarrow> (do _ \<leftarrow> updateSchedContext _ _; updateSchedContext _ _ od);
                                     updateSchedContext _ _ od", symmetric])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (rule stronger_corres_guard_imp)
      apply (rule corres_split[OF  monadic_rewrite_corres'
                                     [OF _ monadic_rewrite_sym
                                             [OF updateSchedContext_decompose_x3[simplified]]]])
                                       (* now use setSchedContext_corres *)
             apply (rule corres_inst[where P="?pred and sc_obj_at n sc_ptr" and P'="?conc and sc_at' sc_ptr"])
             (* one of the sc_obj_at n sc_ptr will be consumed by the next line *)
             apply (rule monadic_rewrite_corres[OF _ update_sched_context_rewrite[where n=n]])
             apply (simp add: updateSchedContext_def)
             apply (rule stronger_corres_guard_imp)
               apply (rule corres_split[OF get_sc_corres])
                 apply (rename_tac sc sc')
                 apply (rule_tac P="?pred and ko_at (kernel_object.SchedContext sc n) sc_ptr"
                             and P'="ko_at' sc' sc_ptr
                                     and K (objBits sc' = minSchedContextBits + n
                                                \<and> 0 < scRefillMax sc' \<and> sc_valid_refills' sc')"
                        in corres_inst)
                apply (rule_tac F="0 < scRefillMax sc' \<and> sc_valid_refills' sc'
                                    \<and> length (scRefills sc') = max_num_refills (min_sched_context_bits + n)"
                        in corres_req)
                  apply clarsimp
                  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps scBits_simps)
                 using scBits_inverse_sc apply fastforce
                 apply (rule stronger_corres_guard_imp)
                   apply (rule setSchedContext_corres)
                    apply (unfold sc_relation_def; elim conjE exE; intro conjI; fastforce?)
                    apply (clarsimp simp: refills_map_def wrap_slice_start_0 hd_map neq_Nil_lengthI
                                          refill_map_def updateAt_def null_def refillHd_def hd_wrap_slice
                                          valid_refills_number'_def max_num_refills_eq_refillAbsoluteMax')
                   apply (clarsimp simp: objBits_simps scBits_simps)
                  apply simp
                 apply (clarsimp simp: obj_at_simps scBits_simps is_sc_obj)
                 apply (fastforce elim!: sc_replies_relation_prevs_list[OF state_relation_sc_replies_relation])
                apply wpsimp
               apply (wpsimp wp: getSchedContext_wp')
              apply (clarsimp simp: obj_at_def is_sc_obj)
             apply (drule state_relation_sc_relation[where ptr=sc_ptr];
                   (fastforce simp: obj_at_simps is_sc_obj obj_bits_def)?)
             apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills_number'_def scBits_simps
                                   opt_map_left_Some valid_refills'_def
                            dest!: scRefills_length)
            apply ((clarsimp simp: objBits_simps)+)[2]
        (* sc_period *)
        apply (rule corres_split[OF updateSchedContext_corres])
             apply (fastforce dest!: state_relation_sc_relation
                               simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some)
            apply (fastforce dest!: state_relation_sc_replies_relation_sc
                              simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some)
           apply (simp add: objBits_simps)
          (* sc_budget *)
          apply (rule corres_split[OF updateSchedContext_corres])
               apply (fastforce dest!: state_relation_sc_relation
                                 simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some)
              apply (fastforce dest!: state_relation_sc_replies_relation_sc
                                simp: obj_at_simps is_sc_obj sc_relation_def opt_map_left_Some)
             apply (simp add: objBits_simps)
            (* the rest *)
            apply (rule_tac P="sc_obj_at n sc_ptr and
                              (\<lambda>s. ((\<lambda>sc. sc_refills sc\<noteq> [] \<and> 0 < sc_refill_max sc) |< scs_of s) sc_ptr)"
                       and P'="sc_at' sc_ptr and
                              (\<lambda>s'. ((\<lambda>ko. 1 < scRefillMax ko \<and> scRefillCount ko = 1 \<and> sc_valid_refills' ko)
                                            |< scs_of' s') sc_ptr)"
                   in corres_inst)
            apply (simp add: when_def[symmetric] whenM_def ifM_def bind_assoc split del: if_split)
            apply (rule corres_guard_imp)
              apply (rule corres_split[OF refillReady_corres]) (* projection version *)
                (* when-block *)
                apply (rule corres_split[OF corres_when], simp)
                   apply (rule corres_split[OF getCurTime_corres])
                     apply (rule corres_guard_imp)
                       apply (rule updateRefillHd_corres, simp)
                       apply (simp add: refill_map_def)
                      apply (simp+)[2]
                    apply (wpsimp+)[2]
                  apply (simp add: liftM_def bind_assoc)
                  apply (rule corres_split[OF get_sc_corres])
                    (* if-block *)
                    apply (rename_tac sc sc')
                    apply (rule_tac P="ko_at (kernel_object.SchedContext sc n) sc_ptr
                                       and K (0 < sc_refill_max sc) and K (sc_refills sc \<noteq> [])
                                        and K (valid_sched_context_size n)"
                                and P'="ko_at' sc' sc_ptr
                                        and K (1 < scRefillMax sc' \<and> scRefillCount sc' = 1 \<and> sc_valid_refills' sc')"
                           in corres_inst)
                    apply (rule_tac F="refill_hd sc = refill_map (refillHd sc')" in corres_req)
                     apply (fastforce dest!: refill_hd_relation)
                    apply (rule corres_guard_imp)
                      apply (rule corres_if)
                        apply (clarsimp simp: refill_map_def)
                       apply (rule corres_split[OF updateRefillHd_corres], simp)
                          apply (clarsimp simp: refill_map_def)
                         apply (rule maybeAddEmptyTail_corres)
                        apply (wpsimp simp: update_refill_hd_rewrite)
                       apply (wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)
                      apply (rule refillAddTail_corres)
                      apply (clarsimp simp: refill_map_def)
                     apply (clarsimp simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_left_Some)
                    apply (clarsimp simp: obj_at_simps opt_map_left_Some is_sc_obj ps_clear_upd
                                          scBits_simps fun_upd_def[symmetric] valid_refills'_def)
                   apply wpsimp
                  apply (wpsimp wp: getSchedContext_wp')
                 apply (wpsimp simp: update_refill_hd_def wp: update_sched_context_wp)
                apply (wpsimp simp: updateRefillHd_def objBits_simps
                                wp: updateSchedContext_wp)
               apply (wpsimp wp: get_sc_refill_ready_wp)
              apply (wpsimp wp: refillReady_wp')
             apply (fastforce simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_left_Some)
            apply (fastforce simp: obj_at_simps ps_clear_upd fun_upd_def[symmetric]
                                   valid_refills'_def opt_map_left_Some)
           apply ((wpsimp wp: updateSchedContext_wp update_sched_context_wp simp: objBits_simps)+)[5]
      apply (rule monadic_rewrite_refine_valid[where P''=\<top>, OF updateSchedContext_decompose_x3, simplified])
          apply ((clarsimp simp: objBits_simps)+)[2]
      apply (wpsimp wp: updateSchedContext_wp simp: objBits_simps)
     apply (clarsimp simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_left_Some)
    apply (clarsimp simp: obj_at_simps scBits_simps ps_clear_upd fun_upd_def[symmetric]
                          valid_refills_number'_def is_sc_obj)
    apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
    apply (fastforce simp: valid_sched_context'_def valid_obj'_def valid_refills_number'_def
                           valid_sched_context_size'_def scBits_simps objBits_simps opt_map_left_Some
                    dest!: scRefills_length)
   apply clarsimp+
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
