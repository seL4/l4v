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

(* FIXME ARMHYP MOVE*)
lemma vcpu_at_ko':
  "vcpu_at' p s \<Longrightarrow> \<exists>vcpu :: vcpu. ko_at' vcpu p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

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
  "\<lbrakk> ko_at' (tcb::tcb) t s ; valid_objs' s ; no_0_obj' s ; atcbVCPUPtr (tcbArch tcb) = Some p \<rbrakk>
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

lemma ko_at_vcpu_at'D:
  "ko_at' (vcpu :: vcpu) vcpuptr s \<Longrightarrow> vcpu_at' vcpuptr s"
  by (fastforce simp: typ_at_to_obj_at_arches elim: obj_at'_weakenE)


(* FIXME: change the original to be predicated! *)
crunch ko_at'2[wp]: doMachineOp "\<lambda>s. P (ko_at' p t s)"
  (simp: crunch_simps)

(* FIXME: change the original to be predicated! *)
crunch pred_tcb_at'2[wp]: doMachineOp "\<lambda>s. P (pred_tcb_at' a b p s)"
  (simp: crunch_simps)

crunch valid_queues'[wp]: readVCPUReg "\<lambda>s. valid_queues s"
  (ignore: getObject)

crunch valid_objs'[wp]: readVCPUReg "\<lambda>s. valid_objs' s"
  (ignore: getObject)

crunch sch_act_wf'[wp]: readVCPUReg "\<lambda>s. P (sch_act_wf (ksSchedulerAction s) s)"
  (ignore: getObject)

crunch ko_at'[wp]: readVCPUReg "\<lambda>s. P (ko_at' a p s)"
  (ignore: getObject)

crunch obj_at'[wp]: readVCPUReg "\<lambda>s. P (obj_at' a p s)"
  (ignore: getObject)

crunch pred_tcb_at'[wp]: readVCPUReg "\<lambda>s. P (pred_tcb_at' a b p s)"
  (ignore: getObject)

crunch ksCurThread[wp]: readVCPUReg "\<lambda>s. P (ksCurThread s)"
  (ignore: getObject)

lemma fromEnum_maxBound_vcpureg_def:
  "fromEnum (maxBound :: vcpureg) = 15"
  by (clarsimp simp: fromEnum_def maxBound_def enum_vcpureg)

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
      by (rule word_eqI[rule_format], rule bits, simp add: word_size)
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
