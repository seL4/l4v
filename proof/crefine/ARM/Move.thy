(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* things that should be moved into first refinement *)

theory Move
imports "../../refine/$L4V_ARCH/Refine"
begin

lemma finaliseCap_Reply:
  "\<lbrace>Q (NullCap,None) and K (isReplyCap cap)\<rbrace> finaliseCapTrue_standin cap fin \<lbrace>Q\<rbrace>"
  apply (rule NonDetMonadVCG.hoare_gen_asm)
  apply (clarsimp simp: finaliseCapTrue_standin_def isCap_simps)
  apply wp
  done

lemma cteDeleteOne_Reply:
  "\<lbrace>st_tcb_at' P t and cte_wp_at' (isReplyCap o cteCap) slot\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (wp finaliseCap_Reply isFinalCapability_inv getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cancelSignal_st_tcb':
  "\<lbrace>\<lambda>s. t\<noteq>t' \<and> st_tcb_at' P t' s\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: cancelSignal_def Let_def)
  apply (rule hoare_pre)
   apply (wp sts_pred_tcb_neq' getNotification_wp|wpc)+
  apply clarsimp
  done

lemma cancelIPC_st_tcb_at':
  "\<lbrace>\<lambda>s. t\<noteq>t' \<and> st_tcb_at' P t' s\<rbrace> cancelIPC t \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: cancelIPC_def Let_def getThreadReplySlot_def locateSlot_conv)
   apply (wp sts_pred_tcb_neq' getEndpoint_wp cteDeleteOne_Reply getCTE_wp'|wpc)+
          apply (rule hoare_strengthen_post [where Q="\<lambda>_. st_tcb_at' P t'"])
           apply (wp threadSet_st_tcb_at2)
           apply simp
          apply (clarsimp simp: cte_wp_at_ctes_of capHasProperty_def)
         apply (wp cancelSignal_st_tcb' sts_pred_tcb_neq' getEndpoint_wp gts_wp'|wpc)+
  apply clarsimp
  done

lemma suspend_st_tcb_at':
  "\<lbrace>\<lambda>s. (t\<noteq>t' \<longrightarrow> st_tcb_at' P t' s) \<and> (t=t' \<longrightarrow> P Inactive)\<rbrace>
  suspend t
  \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: suspend_def unless_def)
  apply (cases "t=t'")
  apply (simp|wp cancelIPC_st_tcb_at' sts_st_tcb')+
  done

lemma to_bool_if:
  "(if w \<noteq> 0 then 1 else 0) = (if to_bool w then 1 else 0)"
  by (auto simp: to_bool_def)

lemma threadGet_wp'':
  "\<lbrace>\<lambda>s. \<forall>v. obj_at' (\<lambda>tcb. f tcb = v) thread s \<longrightarrow> P v s\<rbrace> threadGet f thread \<lbrace>P\<rbrace>"
  apply (rule hoare_pre)
  apply (rule threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedEnqueue_queued_queues_inv:
  "\<lbrace>\<lambda>s.  obj_at' tcbQueued t s \<and> P (ksReadyQueues s) \<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  unfolding tcbSchedEnqueue_def unless_def
  apply (wpsimp simp: if_apply_def2 wp: threadGet_wp)
  apply normalise_obj_at'
  done

lemma addToBitmap_sets_L1Bitmap_same_dom:
  "\<lbrace>\<lambda>s. p \<le> maxPriority \<and> d' = d \<rbrace> addToBitmap d' p
       \<lbrace>\<lambda>rv s. ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrace>"
  unfolding addToBitmap_def bitmap_fun_defs
  apply wpsimp
  apply (clarsimp simp: maxPriority_def numPriorities_def word_or_zero le_def
                        prioToL1Index_max[simplified wordRadix_def, simplified])
  done

crunch ksReadyQueuesL1Bitmap[wp]: setQueue "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"

lemma tcb_in_cur_domain'_def':
  "tcb_in_cur_domain' t = (\<lambda>s. obj_at' (\<lambda>tcb. tcbDomain tcb = ksCurDomain s) t s)"
  unfolding tcb_in_cur_domain'_def
  by (auto simp: obj_at'_def)

lemma sts_running_ksReadyQueuesL1Bitmap[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>
   setThreadState Structures_H.thread_state.Running t
   \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  unfolding setThreadState_def
  apply wp
       apply (rule hoare_pre_cont)
      apply (wpsimp simp: if_apply_def2
                    wp: hoare_drop_imps hoare_vcg_disj_lift threadSet_tcbState_st_tcb_at')+
  done

lemma sts_running_ksReadyQueuesL2Bitmap[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>
   setThreadState Structures_H.thread_state.Running t
   \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  unfolding setThreadState_def
  apply wp
       apply (rule hoare_pre_cont)
      apply (wpsimp simp: if_apply_def2
                    wp: hoare_drop_imps hoare_vcg_disj_lift threadSet_tcbState_st_tcb_at')+
  done

lemma asUser_obj_at_not_queued[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) p\<rbrace> asUser t m \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) p\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

lemma ko_at'_obj_at'_field:
  "ko_at' ko (t s) s \<Longrightarrow> obj_at' (\<lambda>ko'. f ko' = f ko) (t s) s"
  by (erule obj_at'_weakenE, simp)

end
