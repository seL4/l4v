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

context begin interpretation Arch . (*FIXME: arch_split*)

lemma sym_refs_tcb_vcpu':
  "\<lbrakk> ko_at' (tcb::tcb) t s; atcbVCPUPtr (tcbArch tcb) = Some v; sym_refs (state_hyp_refs_of' s) \<rbrakk> \<Longrightarrow>
  \<exists>vcpu. ko_at' vcpu v s \<and> vcpuTCBPtr vcpu = Some t"
  apply (drule (1) hyp_sym_refs_obj_atD')
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (case_tac ko; simp add: tcb_vcpu_refs'_def projectKOs)
  apply (rename_tac koa)
  apply (case_tac koa; clarsimp simp: refs_of_a_def vcpu_tcb_refs'_def)
  done


(* FIXME MOVE *)
lemma ko_at'_tcb_vcpu_not_NULL:
  "\<lbrakk> ko_at' (tcb::tcb) t s ; valid_pspace' s ; atcbVCPUPtr (tcbArch tcb) = Some p \<rbrakk>
   \<Longrightarrow> 0 < p"
  -- "when C pointer is NULL, need this to show atcbVCPUPtr is None"
  unfolding valid_pspace'_def
  by (fastforce simp: valid_tcb'_def valid_arch_tcb'_def word_gt_0 typ_at'_no_0_objD
                dest: valid_objs_valid_tcb')


(* FIXME move *)
lemma setVMRoot_valid_queues':
  "\<lbrace> valid_queues' \<rbrace> setVMRoot a \<lbrace> \<lambda>_. valid_queues' \<rbrace>"
  by (rule valid_queues_lift'; wp)

lemma vcpuEnable_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuEnable a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuSave_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuSave a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuRestore_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuRestore a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuSwitch_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuSwitch a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

end

end
