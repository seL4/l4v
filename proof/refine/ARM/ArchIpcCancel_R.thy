(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpcCancel_R
imports
  IpcCancel_R
begin

context Arch begin arch_global_naming

named_theorems IpcCancel_R_assms

(* FIXME: move to Machine_AI *)
crunch getRegister, setRegister
  for (no_fail) no_fail[intro!, wp, simp]

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
             simp: ARM.nextInstructionRegister_def ARM.faultRegister_def
                   ARM_H.nextInstructionRegister_def ARM_H.faultRegister_def)

lemma archThreadGet_corres:
  "(\<And>a a'. arch_tcb_relation a a' \<Longrightarrow> f a = f' a') \<Longrightarrow>
   corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (arch_thread_get f t) (archThreadGet f' t)"
  unfolding arch_thread_get_def archThreadGet_def
  apply (corresKsimp corres: getObject_TCB_corres)
  apply (clarsimp simp: tcb_relation_def)
  done

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

lemma prepareThreadDelete_corres[corres]:
  "t' = t \<Longrightarrow>
   corres dc (invs and tcb_at t) no_0_obj'
          (prepare_thread_delete t) (prepareThreadDelete t')"
  by (simp add: prepare_thread_delete_def prepareThreadDelete_def)

lemma archThreadSet_tcbQueued[wp]:
  "archThreadSet f tcb \<lbrace>obj_at' (P \<circ> tcbQueued) t\<rbrace>"
  unfolding archThreadSet_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

lemma archThreadSet_st_tcb_at'[wp]:
  "archThreadSet f tcb \<lbrace>st_tcb_at' P t\<rbrace>"
  unfolding archThreadSet_def st_tcb_at'_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

crunch prepareThreadDelete
  for unqueued: "obj_at' (Not \<circ> tcbQueued) t"
  and inactive: "st_tcb_at' ((=) Inactive) t'"
  (simp: obj_at'_not_comp_fold)

lemma setEndpoint_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift')
   apply (simp add: setEndpoint_def)
   apply (rule obj_at_setObject2)
   apply (clarsimp dest!: updateObject_default_result)+
  done

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
     (fact ARM.update_restart_pc_corres
           reply_descendants_of_mdbNext cancel_ipc_pspace_aligned cancel_ipc_pspace_distinct)+

end (* delete_one *)

context delete_one_conc_pre begin

sublocale delete_one_conc_pre_gen
  by unfold_locales
     (fact emptySlot_st_tcb_at')

end (* delete_one_conc_pre *)

end
