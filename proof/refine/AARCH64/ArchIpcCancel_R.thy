(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpcCancel_R
imports
  IpcCancel_R
begin

context Arch begin arch_global_naming

named_theorems IpcCancel_R_assms

crunch Arch.postCapDeletion
  for pred_tcb_at'[IpcCancel_R_assms, wp]: "pred_tcb_at' proj P t"
  and typ_at'[IpcCancel_R_assms, wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: setCTE_pred_tcb_at')

lemma acapClass_not_ReplyClass[IpcCancel_R_assms]:
  "acapClass acap \<noteq> ReplyClass t"
  by (cases acap; simp)

crunch arch_post_cap_deletion
  for pspace_aligned[IpcCancel_R_assms, wp]: "pspace_aligned :: det_state \<Rightarrow> _"
  and pspace_distinct[IpcCancel_R_assms, wp]: "pspace_distinct :: det_state \<Rightarrow> _"
  (simp: crunch_simps wp: crunch_wps)

crunch emptySlot
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

lemma update_restart_pc_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top> (update_restart_pc t) (updateRestartPC t)"
  unfolding update_restart_pc_def updateRestartPC_def
  by (corres corres: asUser_corres'
             simp: AARCH64.nextInstructionRegister_def AARCH64.faultRegister_def
                   AARCH64_H.nextInstructionRegister_def AARCH64_H.faultRegister_def)

lemma archThreadGet_corres:
  "(\<And>a a'. arch_tcb_relation a a' \<Longrightarrow> f a = f' a') \<Longrightarrow>
   corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (arch_thread_get f t) (archThreadGet f' t)"
  unfolding arch_thread_get_def archThreadGet_def
  apply (corresKsimp corres: getObject_TCB_corres)
  apply (clarsimp simp: tcb_relation_def)
  done

lemma tcb_vcpu_relation:
  "arch_tcb_relation a a' \<Longrightarrow> tcb_vcpu a = atcbVCPUPtr a'"
  unfolding arch_tcb_relation_def by auto

lemma archThreadGet_VCPU_corres[corres]:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (arch_thread_get tcb_vcpu t) (archThreadGet atcbVCPUPtr t)"
  by (rule archThreadGet_corres) (erule tcb_vcpu_relation)

lemma archThreadSet_corres:
  assumes "\<And>a a'. arch_tcb_relation a a' \<Longrightarrow> arch_tcb_relation (f a) (f' a')"
  shows "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                (arch_thread_set f t) (archThreadSet f' t)"
proof -
  from assms
  have tcb_rel:
    "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                 tcb_relation (tcb\<lparr>tcb_arch := f (tcb_arch tcb)\<rparr>)
                              (tcbArch_update (\<lambda>_. f' (tcbArch tcb')) tcb')"
    by (simp add: tcb_relation_def)
  show ?thesis
  unfolding arch_thread_set_def archThreadSet_def
  by (corres' \<open>(rotate_tac, erule tcb_rel) |
               (rule ball_tcb_cte_casesI; simp) |
               simp add: tcb_cap_cases_def\<close>
              corres: getObject_TCB_corres setObject_update_TCB_corres')
qed

lemma archThreadSet_VCPU_None_corres[corres]:
  "t = t' \<Longrightarrow> corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
    (arch_thread_set (tcb_vcpu_update Map.empty) t) (archThreadSet (atcbVCPUPtr_update Map.empty) t')"
  apply simp
  apply (rule archThreadSet_corres)
  apply (simp add: arch_tcb_relation_def)
  done

crunch vcpuInvalidateActive
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma getVCPU_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::vcpu) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     in_magnitude_check pageBits_def vcpuBits_def
                     in_monad valid_def obj_at'_def objBits_simps)

lemma dissociateVCPUTCB_corres[corres]:
  "\<lbrakk> v' = v; t' = t \<rbrakk> \<Longrightarrow>
   corres dc (obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_vcpu (tcb_arch tcb) = Some v) t and
              obj_at (\<lambda>ko. \<exists>vcpu. ko = ArchObj (VCPU vcpu) \<and> vcpu_tcb vcpu = Some t) v and
              pspace_aligned and pspace_distinct)
             (no_0_obj')
             (dissociate_vcpu_tcb v t) (dissociateVCPUTCB v' t')"
  unfolding dissociate_vcpu_tcb_def dissociateVCPUTCB_def sanitiseRegister_def sanitise_register_def
  apply (clarsimp simp:  bind_assoc when_fail_assert opt_case_when)
  apply (corres corres: getObject_vcpu_corres setObject_VCPU_corres asUser_corres'
                simp: vcpu_relation_def archThreadSet_def tcb_ko_at' tcb_at_typ_at')
            apply (wpsimp simp: tcb_at_typ_at' archThreadGet_def
                          wp: get_vcpu_wp getVCPU_wp arch_thread_get_wp getObject_tcb_wp)+
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb in_omonad)
  apply (clarsimp simp: pred_tcb_at_def)
  apply normalise_obj_at'
  apply (rule context_conjI)
   apply (rule vcpu_at_cross; assumption?)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac tcb vcpu)
  apply (prop_tac "ko_at (TCB tcb) t s", clarsimp simp: obj_at_def)
  apply (drule (3) ko_tcb_cross)
  apply (prop_tac "ako_at (VCPU vcpu) v s", clarsimp simp: obj_at_def)
  apply (drule (3) ko_vcpu_cross)
  apply normalise_obj_at'
  apply (clarsimp simp: tcb_relation_def arch_tcb_relation_def vcpu_relation_def)
  done

lemma sym_refs_tcb_vcpu:
  "\<lbrakk> ko_at (TCB tcb) t s; tcb_vcpu (tcb_arch tcb) = Some v; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
  \<exists>vcpu. ko_at (ArchObj (VCPU vcpu)) v s \<and> vcpu_tcb vcpu = Some t"
  apply (drule (1) hyp_sym_refs_obj_atD)
  apply (clarsimp simp: obj_at_def hyp_refs_of_def)
  apply (rename_tac ko)
  apply (case_tac ko; simp add: tcb_vcpu_refs_def split: option.splits)
  apply (rename_tac koa)
  apply (case_tac koa; simp add: vcpu_tcb_refs_def split: option.splits)
  done

lemma fpuRelease_corres[corres]:
  "t' = t \<Longrightarrow>
   corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu) \<top> (fpu_release t) (fpuRelease t')"
  by (corres simp: fpu_release_def fpuRelease_def)

lemma prepareThreadDelete_corres[corres]:
  "t' = t \<Longrightarrow>
   corres dc (invs and tcb_at t) no_0_obj'
          (prepare_thread_delete t) (prepareThreadDelete t')"
  apply (simp add: prepare_thread_delete_def prepareThreadDelete_def)
  apply (corres corres: archThreadGet_corres
                wp: arch_thread_get_wp getObject_tcb_wp hoare_vcg_op_lift
                simp: archThreadGet_def
         | corres_cases_both)+
   apply (fastforce dest: sym_refs_tcb_vcpu simp: obj_at_def)
  apply (clarsimp simp: tcb_ko_at')
  done

crunch vcpuInvalidateActive
  for no_vcpu[wp]: "\<lambda>s. P (obj_at' (P'::'a:: no_vcpu \<Rightarrow> bool) t s)"

lemma archThreadSet_tcbQueued[wp]:
  "archThreadSet f tcb \<lbrace>obj_at' (P \<circ> tcbQueued) t\<rbrace>"
  unfolding archThreadSet_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

lemma dissociateVCPUTCB_unqueued[wp]:
  "dissociateVCPUTCB vcpu tcb \<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  unfolding dissociateVCPUTCB_def archThreadGet_def by (wpsimp simp: o_def)

lemmas setObject_vcpu_st_tcb_at'[wp] =
  setObject_vcpu_obj_at'_no_vcpu [where P'="P' o tcbState" for P', folded st_tcb_at'_def]
lemmas vcpuInvalidateActive_st_tcb_at'[wp] =
  vcpuInvalidateActive_no_vcpu [where P'="P' o tcbState" for P', folded st_tcb_at'_def]

lemma archThreadSet_st_tcb_at'[wp]:
  "archThreadSet f tcb \<lbrace>st_tcb_at' P t\<rbrace>"
  unfolding archThreadSet_def st_tcb_at'_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

lemma dissociateVCPUTCB_st_tcb_at'[wp]:
  "dissociateVCPUTCB vcpu tcb \<lbrace>st_tcb_at' P t'\<rbrace>"
  unfolding dissociateVCPUTCB_def archThreadGet_def by wpsimp

crunch dissociateVCPUTCB
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps setObject_queues_unchanged_tcb simp: crunch_simps)

crunch fpuRelease
  for st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P t s)"
  and valid_objs'[wp]: valid_objs'
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"

crunch prepareThreadDelete
  for unqueued: "obj_at' (Not \<circ> tcbQueued) t"
  and inactive: "st_tcb_at' ((=) Inactive) t'"
  (simp: obj_at'_not_comp_fold)

end (* Arch *)

interpretation IpcCancel_R?: IpcCancel_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact IpcCancel_R_assms)?)?)
qed

(* instantiate locales with assumptions depending on IpcCancel_R instantiation *)

context delete_one begin

sublocale delete_one_gen
  by unfold_locales
     (fact AARCH64.update_restart_pc_corres
           reply_descendants_of_mdbNext cancel_ipc_pspace_aligned cancel_ipc_pspace_distinct)+

end (* delete_one *)

context delete_one_conc_pre begin

sublocale delete_one_conc_pre_gen
  by unfold_locales
     (fact emptySlot_st_tcb_at')

end (* delete_one_conc_pre *)

end
