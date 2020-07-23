(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Reply_R
imports TcbAcc_R
begin

crunches setReplyTCB for
  pred_tcb_at'[wp]: "pred_tcb_at' proj test t"

lemma replyUnlink_st_tcb_at'_wp:
  "\<lbrace>\<lambda>s. reply_at' rptr s \<longrightarrow>
          obj_at' (\<lambda>reply.
                      (replyTCB reply = Some tptr \<longrightarrow> test Inactive) \<and>
                      (replyTCB reply \<noteq> Some tptr \<longrightarrow> st_tcb_at' test tptr s))
                  rptr s\<rbrace>
   replyUnlink rptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: sts_st_tcb' hoare_vcg_if_lift2 hoare_vcg_imp_lift hoare_vcg_disj_lift
              simp: getReplyTCB_def
         split_del: if_split)
  apply (fastforce simp: obj_at'_def)
  done

lemma replyUnlink_st_tcb_at'_Inactive:
  "\<lbrace>\<lambda>s. st_tcb_at' test tptr s \<and> test Inactive\<rbrace>
   replyUnlink rptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  apply (wpsimp wp: replyUnlink_st_tcb_at'_wp)
  done

lemma replyUnlink_st_tcb_at'_sym_ref:
  "\<lbrace>\<lambda>s. reply_at' rptr s \<longrightarrow>
          obj_at' (\<lambda>reply. replyTCB reply = Some tptr) rptr s \<and> test Inactive\<rbrace>
   replyUnlink rptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  apply (wpsimp wp: replyUnlink_st_tcb_at'_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma replyRemoveTCB_st_tcb_at'_Inactive:
  "\<lbrace>\<lambda>s. tcb_at' tptr s \<longrightarrow> st_tcb_at' test tptr s \<and> test Inactive\<rbrace>
   replyRemoveTCB tptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: hoare_drop_imp (* FIXME: dangerous, but necessary to avoid the goal blowing
                                             up in size *)
                    hoare_vcg_if_lift hoare_vcg_all_lift replyUnlink_st_tcb_at'_Inactive
              simp: cleanReply_def
         split_del: if_split)
  done

lemma replyUnlink_tcb_obj_at'_no_change:
  "\<lbrace>(\<lambda>s. P (obj_at' Q tptr s)) and
    K (\<forall>tcb st. (Q (tcbState_update (\<lambda>_. Inactive) tcb) = Q tcb) \<and>
                (Q (tcbState_update (\<lambda>_. replyObject_update Map.empty st) tcb) = Q tcb) \<and>
                (Q (tcbQueued_update (\<lambda>_. True) tcb) = Q tcb))\<rbrace>
   replyUnlink rptr
   \<lbrace>\<lambda>_ s. P (obj_at' Q tptr s)\<rbrace>"
  unfolding replyUnlink_def scheduleTCB_def rescheduleRequired_def
            setReplyTCB_def getReplyTCB_def
  apply (rule hoare_gen_asm)
  supply set_reply'.get_wp[wp del]
  apply (wpsimp wp: hoare_vcg_if_lift2 tcbSchedEnqueue_tcb_obj_at'_no_change set_reply'.get_inv
                    isSchedulable_inv hoare_vcg_imp_lift setThreadState_tcb_obj_at'_no_change
                    set_reply'.get_wp_rv_only threadSet_obj_at'_simple_strongest
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where a="getReply rptr" and P="\<lambda>rv s. \<not>tcb_at' (P rv) s" for P]
              simp: o_def)
  done

end