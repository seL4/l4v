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
  "\<lbrace>\<lambda>s. \<forall>reply :: reply. ko_at' reply rptr s \<longrightarrow>
          (if replyTCB reply = Some tptr
           then test Inactive
           else st_tcb_at' test tptr s)\<rbrace>
   replyUnlink rptr
   \<lbrace>\<lambda>_. st_tcb_at' test tptr\<rbrace>"
  unfolding replyUnlink_def
  apply (wpsimp wp: sts_st_tcb' hoare_vcg_if_lift2 hoare_vcg_imp_lift hoare_vcg_disj_lift
              simp: getReplyTCB_def
         split_del: if_split)
  apply (fastforce simp: obj_at'_def)
  done

lemma replyUnlink_simple':
  "replyUnlink rptr \<lbrace>st_tcb_at' simple' tptr\<rbrace>"
  by (wpsimp wp: replyUnlink_st_tcb_at'_wp)

lemma replyRemoveTCB_simple':
  "replyRemoveTCB t \<lbrace>st_tcb_at' simple' t'\<rbrace>"
  unfolding replyRemoveTCB_def
  apply (wpsimp wp: hoare_drop_imp (* FIXME: dangerous, but necessary to avoid the goal blowing
                                             up in size *)
                    hoare_vcg_if_lift hoare_vcg_all_lift replyUnlink_simple'
              simp: cleanReply_def
         split_del: if_split)
  done

end