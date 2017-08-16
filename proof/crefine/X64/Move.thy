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

(* FIXME MOVE *)
lemma typ_at'_no_0_objD:
  "typ_at' P p s \<Longrightarrow> no_0_obj' s \<Longrightarrow> p \<noteq> 0"
  by (cases "p = 0" ; clarsimp)

(* FIXME ARMHYP MOVE *)
lemma ko_at'_not_NULL:
  "\<lbrakk> ko_at' ko p s ; no_0_obj' s\<rbrakk>
   \<Longrightarrow> p \<noteq> 0"
  by (fastforce simp:  word_gt_0 typ_at'_no_0_objD)

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME move *)
lemma setVMRoot_valid_queues':
  "\<lbrace> valid_queues' \<rbrace> setVMRoot a \<lbrace> \<lambda>_. valid_queues' \<rbrace>"
  by (rule valid_queues_lift'; wp)

(* FIXME: change the original to be predicated! *)
crunch ko_at'2[wp]: doMachineOp "\<lambda>s. P (ko_at' p t s)"
  (simp: crunch_simps)

(* FIXME: change the original to be predicated! *)
crunch pred_tcb_at'2[wp]: doMachineOp "\<lambda>s. P (pred_tcb_at' a b p s)"
  (simp: crunch_simps)

end

(* FIXME move *)
lemma shiftr_and_eq_shiftl:
  fixes w x y :: "'a::len word"
  assumes r: "(w >> n) && x = y"
  shows "w && (x << n) = (y << n)"
  using assms
  proof -
    { fix i
      assume i: "i < LENGTH('a)"
      hence "test_bit (w && (x << n)) i \<longleftrightarrow> test_bit (y << n) i"
        using word_eqD[where x="i-n", OF r]
        by (cases "n \<le> i") (auto simp: nth_shiftl nth_shiftr)
    } note bits = this
    show ?thesis
      by (rule word_eqI, rule bits, simp add: word_size)
  qed

(* FIXME: move *)
lemma cond_throw_whenE:
   "(if P then f else throwError e) = (whenE (\<not> P) (throwError e) >>=E (\<lambda>_. f))"
   by (auto split: if_splits
             simp: throwError_def bindE_def
                   whenE_def bind_def returnOk_def return_def)

lemma ksPSpace_update_eq_ExD:
  "s = t\<lparr> ksPSpace := ksPSpace s\<rparr>
     \<Longrightarrow> \<exists>ps. s = t \<lparr> ksPSpace := ps \<rparr>"
  by (erule exI)


end
