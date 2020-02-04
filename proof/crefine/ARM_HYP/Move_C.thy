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

theory Move_C
imports "Refine.Refine"
begin

(* FIXME move: need a theory on top of CSpec that arches can share *)
(* word size corresponding to a C int (e.g. 32 bit signed on x64 and ARM *)
type_synonym int_sword = "machine_word_len signed word"

lemma finaliseCap_Reply:
  "\<lbrace>Q (NullCap,NullCap) and K (isReplyCap cap)\<rbrace> finaliseCapTrue_standin cap fin \<lbrace>Q\<rbrace>"
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
  apply (simp add: suspend_def)
  unfolding updateRestartPC_def
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

lemma vcpu_at_ko'_eq:
  "(\<exists>vcpu :: vcpu. ko_at' vcpu p s) = vcpu_at' p s"
  apply (rule iffI)
   apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

lemmas vcpu_at_ko' = vcpu_at_ko'_eq[THEN iffD2]

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
  \<comment> \<open>when C pointer is NULL, need this to show atcbVCPUPtr is None\<close>
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

crunch valid_objs'[wp]: readVCPUReg "\<lambda>s. valid_objs' s"

crunch sch_act_wf'[wp]: readVCPUReg "\<lambda>s. P (sch_act_wf (ksSchedulerAction s) s)"

crunch ko_at'[wp]: readVCPUReg "\<lambda>s. P (ko_at' a p s)"

crunch obj_at'[wp]: readVCPUReg "\<lambda>s. P (obj_at' a p s)"

crunch pred_tcb_at'[wp]: readVCPUReg "\<lambda>s. P (pred_tcb_at' a b p s)"

crunch ksCurThread[wp]: readVCPUReg "\<lambda>s. P (ksCurThread s)"

lemma fromEnum_maxBound_vcpureg_def:
  "fromEnum (maxBound :: vcpureg) = 42"
  by (clarsimp simp: fromEnum_def maxBound_def enum_vcpureg)

lemma unat_of_nat_mword_fromEnum_vcpureg[simp]:
  "unat ((of_nat (fromEnum e)) :: machine_word) = fromEnum (e :: vcpureg)"
  apply (subst unat_of_nat_eq, clarsimp)
   apply (rule order_le_less_trans[OF maxBound_is_bound])
   apply (clarsimp simp: fromEnum_maxBound_vcpureg_def)+
  done

lemma unat_of_nat_mword_length_upto_vcpureg[simp]:
  "unat ((of_nat (length [(start :: vcpureg) .e. end])) :: machine_word) = length [start .e. end]"
  apply (subst unat_of_nat_eq ; clarsimp)
  apply (rule order_le_less_trans[OF length_upto_enum_le_maxBound])
  apply (simp add: fromEnum_maxBound_vcpureg_def)
  done

lemma fromEnum_maxBound_vppievent_irq_def:
  "fromEnum (maxBound :: vppievent_irq) = 0"
  by (clarsimp simp: fromEnum_def maxBound_def enum_vppievent_irq)

(* when creating a new object, the entire slot including starting address should be free *)
(* FIXME move *)
lemma ps_clear_entire_slotI:
  "({p..p + 2 ^ n - 1}) \<inter> dom (ksPSpace s) = {} \<Longrightarrow> ps_clear p n s"
  by (fastforce simp: ps_clear_def)

(* FIXME move *)
lemma ps_clear_ksPSpace_upd_same[simp]:
  "ps_clear p n (s\<lparr>ksPSpace := ksPSpace s(p \<mapsto> v)\<rparr>) = ps_clear p n s"
  by (fastforce simp: ps_clear_def)

(* FIXME move *)
lemma getObject_vcpu_prop:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(vcpu :: vcpu) s. P vcpu\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad projectKOs)
  done

(* FIXME move *)
(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma setObject_sets_object_vcpu:
  "\<lbrace> vcpu_at' v \<rbrace> setObject v (vcpu::vcpu) \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: setObject_def updateObject_default_def bind_assoc)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift simp: alignError_def)
  apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def dest!: vcpu_at_ko')
  apply (fastforce simp: fun_upd_apply)
  done

(* FIXME move *)
(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma placeNewObject_creates_object_vcpu:
  "\<lbrace> \<top> \<rbrace> placeNewObject v (vcpu::vcpu) 0 \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del] haskell_assert_inv[wp del]
  apply (clarsimp simp: placeNewObject_def placeNewObject'_def split_def alignError_def)
  apply (wpsimp wp: assert_wp hoare_vcg_imp_lift' hoare_vcg_ex_lift)
  apply (clarsimp simp: is_aligned_mask[symmetric] objBitsKO_def archObjSize_def)
  apply (case_tac "is_aligned v vcpuBits"; clarsimp)
  apply (rule conjI; clarsimp)
   apply (subst (asm) lookupAround2_None1)
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def fun_upd_apply)
   apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps fun_upd_apply)
  apply (subst (asm) lookupAround2_char1)
  apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def fun_upd_apply)
  apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps)
  done

end


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
