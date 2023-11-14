(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_C
imports Delete_C Ipc_C
begin

lemma getObject_sched:
  "(x::tcb, s') \<in> fst (getObject t s) \<Longrightarrow>
  (x,s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (getObject t (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: in_monad getObject_def split_def loadObject_default_def
                        magnitudeCheck_def projectKOs
                  split: option.splits)
  done

lemma threadGet_sched:
  "(x, s') \<in> fst (threadGet t f s) \<Longrightarrow>
  (x,s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (threadGet t f (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: in_monad threadGet_def liftM_def)
  apply (drule getObject_sched)
  apply fastforce
  done

lemma setObject_sched:
  "(x, s') \<in> fst (setObject t (v::tcb) s) \<Longrightarrow>
  (x, s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (setObject t v (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: in_monad setObject_def split_def updateObject_default_def
                        magnitudeCheck_def projectKOs
                  split: option.splits)
  done

lemma threadSet_sched:
  "(x, s') \<in> fst (threadSet f t s) \<Longrightarrow>
  (x,s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (threadSet f t (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: in_monad threadSet_def)
  apply (drule getObject_sched)
  apply (drule setObject_sched)
  apply fastforce
  done

lemma asUser_sched:
  "(rv,s') \<in> fst (asUser t f s) \<Longrightarrow>
  (rv,s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (asUser t f (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: asUser_def split_def in_monad select_f_def)
  apply (drule threadGet_sched)
  apply (drule threadSet_sched)
  apply fastforce
  done

lemma doMachineOp_sched:
  "(rv,s') \<in> fst (doMachineOp f s) \<Longrightarrow>
  (rv,s'\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>) \<in> fst (doMachineOp f (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>))"
  apply (clarsimp simp: doMachineOp_def split_def in_monad select_f_def)
  apply fastforce
  done

context begin interpretation Arch . (*FIXME: arch_split*)
crunch queues[wp]: setupReplyMaster "valid_queues"
  (simp: crunch_simps wp: crunch_wps)

crunch curThread [wp]: restart "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)
end

context kernel_m
begin

lemma getMRs_rel_sched:
  "\<lbrakk> getMRs_rel args buffer s;
     (cur_tcb' and case_option \<top> valid_ipc_buffer_ptr' buffer) s \<rbrakk>
  \<Longrightarrow> getMRs_rel args buffer (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>)"
  apply (clarsimp simp: getMRs_rel_def)
  apply (rule exI, rule conjI, assumption)
  apply (subst det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def split: option.splits)
   apply (simp add: valid_ipc_buffer_ptr'_def)
  apply (subst (asm) det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def)
  apply (clarsimp simp: getMRs_def in_monad)
  apply (drule asUser_sched)
  apply (intro exI)
  apply (erule conjI)
  apply (cases buffer)
   apply (simp add: return_def)
  apply clarsimp
  apply (drule mapM_upd [rotated])
   prefer 2
   apply fastforce
  apply (clarsimp simp: loadWordUser_def in_monad stateAssert_def word_size)
  apply (erule doMachineOp_sched)
  done

lemma getObject_state:
  " \<lbrakk>(x, s') \<in> fst (getObject t' s); ko_at' ko t s\<rbrakk>
  \<Longrightarrow> (if t = t' then tcbState_update (\<lambda>_. st) x else x,
      s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>)
      \<in> fst (getObject t' (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>))"
  apply (simp split: if_split)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: getObject_def split_def loadObject_default_def in_monad
                         Corres_C.in_magnitude_check' projectKOs objBits_simps')
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs objBits_simps)
   apply (simp add: magnitudeCheck_def in_monad split: option.splits)
   apply clarsimp
   apply (simp add: lookupAround2_char2)
   apply (clarsimp split: if_split_asm)
   apply (erule_tac x=x2 in allE)
   apply (clarsimp simp: ps_clear_def)
   apply (drule_tac x=x2 in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply simp
   apply (erule notE, rule word_diff_ls'(3))
    apply unat_arith
   apply (drule is_aligned_no_overflow, simp add: word_bits_def)
  apply clarsimp
  apply (clarsimp simp: getObject_def split_def loadObject_default_def in_monad
                        Corres_C.in_magnitude_check' projectKOs objBits_simps')
  apply (simp add: magnitudeCheck_def in_monad split: option.splits)
  apply clarsimp
  apply (simp add: lookupAround2_char2)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x=t in allE)
   apply simp
   apply (clarsimp simp: obj_at'_real_def projectKOs
                         ko_wp_at'_def objBits_simps)
   apply (simp add: ps_clear_def)
   apply (drule_tac x=t in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply simp
   apply (erule notE, rule word_diff_ls'(3))
    apply unat_arith
   apply (drule is_aligned_no_overflow)
   apply simp
  apply (erule_tac x=x2 in allE)
  apply (clarsimp simp: ps_clear_def)
  apply (drule_tac x=x2 in orthD2)
   apply fastforce
  apply clarsimp
  apply (erule impE)
   apply (rule word_diff_ls'(3))
   apply unat_arith
   apply (drule is_aligned_no_overflow)
   apply simp
  apply fastforce
  done


lemma threadGet_state:
  "\<lbrakk> (uc, s') \<in> fst (threadGet (atcbContextGet o tcbArch) t' s); ko_at' ko t s \<rbrakk> \<Longrightarrow>
   (uc, s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>) \<in>
  fst (threadGet (atcbContextGet o tcbArch) t' (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>))"
  apply (clarsimp simp: threadGet_def liftM_def in_monad)
  apply (drule (1) getObject_state [where st=st])
  apply (rule exI)
  apply (erule conjI)
  apply (simp split: if_splits)
  done

lemma asUser_state:
  "\<lbrakk>(x,s) \<in> fst (asUser t' f s); ko_at' ko t s; \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace> \<rbrakk> \<Longrightarrow>
  (x,s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>) \<in>
  fst (asUser t' f (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>))"
  apply (clarsimp simp: asUser_def in_monad select_f_def)
  apply (frule use_valid, rule threadGet_inv [where P="(=) s"], rule refl)
  apply (frule use_valid, assumption, rule refl)
  apply clarsimp
  apply (frule (1) threadGet_state)
  apply (intro exI)
  apply (erule conjI)
  apply (rule exI, erule conjI)
  apply (clarsimp simp: threadSet_def in_monad)
  apply (frule use_valid, rule getObject_inv [where P="(=) s"])
    apply (simp add: loadObject_default_def)
    apply wp
    apply simp
   apply (rule refl)
  apply clarsimp
  apply (frule (1) getObject_state)
  apply (intro exI)
  apply (erule conjI)
  apply (clarsimp simp: setObject_def split_def updateObject_default_def threadGet_def
                        in_magnitude_check' getObject_def loadObject_default_def liftM_def
                        objBits_simps' projectKOs in_monad)
  apply (simp split: if_split)
  apply (rule conjI)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
   apply (clarsimp simp: magnitudeCheck_def in_monad split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (cases s, simp)
    apply (rule ext)
    apply (clarsimp split: if_split)
    apply (cases ko)
    apply clarsimp
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp add: lookupAround2_char2 split: if_split_asm)
    apply (erule_tac x=x2 in allE)
    apply simp
    apply (simp add: ps_clear_def)
    apply (drule_tac x=x2 in orthD2)
     apply fastforce
    apply clarsimp
    apply (erule impE, simp)
    apply (erule notE, rule word_diff_ls'(3))
     apply unat_arith
    apply (drule is_aligned_no_overflow)
    apply simp
   apply (rule exI)
   apply (rule conjI, fastforce)
   apply clarsimp
   apply (cases s, clarsimp)
   apply (rule ext, clarsimp split: if_split)
   apply (cases ko, clarsimp)
  apply (clarsimp simp: magnitudeCheck_def in_monad split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (cases s, clarsimp)
   apply (rule ext, clarsimp split: if_split)
   apply (case_tac tcb, clarsimp)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp add: lookupAround2_char2 split: if_split_asm)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs objBits_simps)
    apply (erule_tac x=t in allE)
    apply simp
    apply (simp add: ps_clear_def)
    apply (drule_tac x=t in orthD2)
     apply fastforce
    apply clarsimp
    apply (erule impE, simp)
    apply (erule notE, rule word_diff_ls'(3))
     apply unat_arith
    apply (drule is_aligned_no_overflow)
    apply simp
   apply (erule_tac x=x2 in allE)
   apply simp
   apply (simp add: ps_clear_def)
   apply (drule_tac x=x2 in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply (rule word_diff_ls'(3))
     apply unat_arith
    apply (drule is_aligned_no_overflow)
    apply simp
   apply (erule impE, simp)
   apply simp
  apply (rule exI)
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (cases s, clarsimp)
  apply (rule ext, clarsimp split: if_split)
  apply (case_tac tcb, clarsimp)
  done

lemma doMachineOp_state:
  "(rv,s') \<in> fst (doMachineOp f s) \<Longrightarrow>
  (rv,s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>)
  \<in> fst (doMachineOp f (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>))"
  apply (clarsimp simp: doMachineOp_def split_def in_monad select_f_def)
  apply fastforce
  done

lemma mapM_upd_inv:
  assumes f: "\<And>x rv. (rv,s) \<in> fst (f x s) \<Longrightarrow> x \<in> set xs \<Longrightarrow> (rv, g s) \<in> fst (f x (g s))"
  assumes inv: "\<And>x. \<lbrace>(=) s\<rbrace> f x \<lbrace>\<lambda>_. (=) s\<rbrace>"
  shows "(rv,s) \<in> fst (mapM f xs s) \<Longrightarrow> (rv, g s) \<in> fst (mapM f xs (g s))"
  using f inv
proof (induct xs arbitrary: rv s)
  case Nil
  thus ?case by (simp add: mapM_Nil return_def)
next
  case (Cons z zs)
  from Cons.prems
  show ?case
    apply (clarsimp simp: mapM_Cons in_monad)
    apply (frule use_valid, assumption, rule refl)
    apply clarsimp
    apply (drule Cons.prems, simp)
    apply (rule exI, erule conjI)
    apply (drule Cons.hyps)
      apply simp
     apply assumption
    apply simp
    done
qed

lemma getMRs_rel_state:
  "\<lbrakk>getMRs_rel args buffer s;
    (cur_tcb' and case_option \<top> valid_ipc_buffer_ptr' buffer) s;
    ko_at' ko t s \<rbrakk> \<Longrightarrow>
  getMRs_rel args buffer (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbState_update (\<lambda>_. st) ko))\<rparr>)"
  apply (clarsimp simp: getMRs_rel_def)
  apply (rule exI, erule conjI)
  apply (subst (asm) det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def)
  apply (subst det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def)
   apply (rule conjI)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs
                          objBits_simps ps_clear_def split: if_split)
   apply (clarsimp simp: valid_ipc_buffer_ptr'_def split: option.splits)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def projectKOs obj_at'_real_def
                         objBits_simps ps_clear_def split: if_split)
  apply (clarsimp simp: getMRs_def in_monad)
  apply (frule use_valid, rule asUser_inv [where P="(=) s"])
    apply (wp mapM_wp' getRegister_inv)[1]
   apply simp
  apply clarsimp
  apply (drule (1) asUser_state)
   apply (wp mapM_wp' getRegister_inv)[1]
  apply (intro exI)
  apply (erule conjI)
  apply (cases buffer)
   apply (clarsimp simp: return_def)
  apply clarsimp
  apply (drule mapM_upd_inv [rotated -1])
    prefer 3
    apply fastforce
   prefer 2
   apply wp
  apply (clarsimp simp: loadWordUser_def in_monad stateAssert_def word_size
                  simp del: fun_upd_apply)
  apply (rule conjI)
   apply (clarsimp simp: pointerInUserData_def typ_at'_def ko_wp_at'_def
                         projectKOs ps_clear_def obj_at'_real_def
                  split: if_split)
  apply (erule doMachineOp_state)
  done

lemma setThreadState_getMRs_rel:
  "\<lbrace>getMRs_rel args buffer and cur_tcb' and case_option \<top> valid_ipc_buffer_ptr' buffer
           and (\<lambda>_. runnable' st)\<rbrace>
      setThreadState st t \<lbrace>\<lambda>_. getMRs_rel args buffer\<rbrace>"
  apply (rule hoare_gen_asm')
  apply (simp add: setThreadState_runnable_simp)
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: setObject_def split_def updateObject_default_def)
   apply wp
  apply (simp del: fun_upd_apply)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp del: fun_upd_apply)
  apply (drule obj_at_ko_at')+
  apply (clarsimp simp del: fun_upd_apply)
  apply (rule exI, rule conjI, assumption)
  apply (clarsimp split: if_split simp del: fun_upd_apply)
  apply (simp add: getMRs_rel_state)
  done

lemma setThreadState_sysargs_rel:
  "\<lbrace>sysargs_rel args buffer and (\<lambda>_. runnable' st)\<rbrace> setThreadState st t \<lbrace>\<lambda>_. sysargs_rel args buffer\<rbrace>"
  apply (cases buffer, simp_all add: sysargs_rel_def)
   apply (rule hoare_pre)
   apply (wp setThreadState_getMRs_rel hoare_valid_ipc_buffer_ptr_typ_at'|simp)+
  done

lemma ccorres_abstract_known:
  "\<lbrakk> \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' g (g' rv'); ccorres rvr xf P P' hs f (g' val) \<rbrakk>
     \<Longrightarrow> ccorres rvr xf P (P' \<inter> {s. xf' s = val}) hs f g"
  apply (rule ccorres_guard_imp2)
   apply (rule_tac xf'=xf' in ccorres_abstract)
    apply assumption
   apply (rule_tac P="rv' = val" in ccorres_gen_asm2)
   apply simp
  apply simp
  done

lemma distinct_remove1_filter:
  "distinct xs \<Longrightarrow> remove1 v xs = [x\<leftarrow>xs. x \<noteq> v]"
  apply (induct xs)
   apply simp
  apply (clarsimp split: if_split)
  apply (rule sym, simp add: filter_id_conv)
  apply clarsimp
  done

lemma hrs_mem_update_cong:
  "\<lbrakk> \<And>x. f x = f' x \<rbrakk> \<Longrightarrow> hrs_mem_update f = hrs_mem_update f'"
  by (simp add: hrs_mem_update_def)

lemma setPriority_ccorres:
  "ccorres dc xfdc
      (\<lambda>s. tcb_at' t s \<and> Invariants_H.valid_queues s \<and>  ksCurDomain s \<le> maxDomain \<and>
           valid_queues' s \<and> valid_objs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> (priority \<le> maxPriority))
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr t} \<inter> {s. prio_' s = ucast priority})
      [] (setPriority t priority) (Call setPriority_'proc)"
  apply (cinit lift: tptr_' prio_')
   apply (ctac(no_vcg) add: tcbSchedDequeue_ccorres)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule threadSet_ccorres_lemma2[where P=\<top>])
        apply vcg
       apply clarsimp
       apply (erule(1) rf_sr_tcb_update_no_queue2,
              (simp add: typ_heap_simps')+, simp_all?)[1]
        apply (rule ball_tcb_cte_casesI, simp+)
       apply (simp add: ctcb_relation_def)
      apply (ctac(no_vcg) add: isRunnable_ccorres)
       apply (simp add: when_def to_bool_def del: Collect_const)
       apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
        apply (rule ccorres_pre_getCurThread)
        apply (rule_tac R = "\<lambda>s. rv = ksCurThread s" in ccorres_cond2)
          apply (clarsimp simp: rf_sr_ksCurThread)
         apply (ctac add: rescheduleRequired_ccorres)
        apply (ctac add: possibleSwitchTo_ccorres)
       apply (rule ccorres_return_Skip')
      apply (wp isRunnable_wp)
     apply (wpsimp wp: hoare_drop_imps threadSet_valid_queues threadSet_valid_objs'
                       weak_sch_act_wf_lift_linear threadSet_pred_tcb_at_state
                       threadSet_tcbDomain_triv
                 simp: st_tcb_at'_def o_def split: if_splits)
    apply (simp add: guard_is_UNIV_def)
   apply (rule hoare_strengthen_post[
                 where Q="\<lambda>rv s.
                          obj_at' (\<lambda>_. True) t s \<and>
                          priority \<le> maxPriority \<and>
                          Invariants_H.valid_queues s \<and>
                          ksCurDomain s \<le> maxDomain \<and>
                          valid_objs' s \<and>
                          valid_queues' s \<and>
                          weak_sch_act_wf (ksSchedulerAction s) s \<and>
                          (\<forall>d p. \<not> t \<in> set (ksReadyQueues s (d, p)))"])
    apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_valid_queues tcbSchedDequeue_nonq)
   apply (clarsimp simp: valid_tcb'_tcbPriority_update)
  apply clarsimp
  apply (frule (1) valid_objs'_maxDomain[where t=t])
  apply (frule (1) valid_objs'_maxPriority[where t=t])
  apply simp
  done

lemma setMCPriority_ccorres:
  "ccorres dc xfdc
      (invs' and tcb_at' t and (\<lambda>s. priority \<le> maxPriority))
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr t} \<inter> {s. mcp_' s = ucast priority})
      [] (setMCPriority t priority) (Call setMCPriority_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: tptr_' mcp_')
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule threadSet_ccorres_lemma2[where P=\<top>])
    apply vcg
   apply clarsimp
   apply (erule(1) rf_sr_tcb_update_no_queue2,
              (simp add: typ_heap_simps')+)[1]
    apply (rule ball_tcb_cte_casesI, simp+)
   apply (simp add: ctcb_relation_def cast_simps)
  apply (clarsimp simp: down_cast_same [symmetric] ucast_up_ucast is_up is_down)
  done

lemma ccorres_subgoal_tailE:
  "\<lbrakk> ccorres rvr xf Q Q' hs (b ()) d;
      ccorres rvr xf Q Q' hs (b ()) d \<Longrightarrow> ccorres rvr xf P P' hs (a >>=E b) (c ;; d) \<rbrakk>
        \<Longrightarrow> ccorres rvr xf P P' hs (a >>=E b) (c ;; d)"
  by simp

lemma checkCapAt_ccorres:
  "\<lbrakk> \<And>rv' t t'. ceqv \<Gamma> ret__unsigned_long_' rv' t t' c (c' rv');
      ccorres rvr xf P P' hs (f >>= g) (c' (scast true));
      ccorres rvr xf Q Q' hs (g ()) (c' (scast false));
      guard_is_UNIV dc xfdc (\<lambda>_ _. P' \<inter> Q') \<rbrakk>
    \<Longrightarrow> ccorres rvr xf (invs' and valid_cap' cap and P and Q)
                       (UNIV \<inter> {s. ccap_relation cap cap'} \<inter> {s. slot' = cte_Ptr slot}) hs
         (checkCapAt cap slot f >>= g)
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t slot'\<rbrace>
            (\<acute>ret__unsigned_long :== CALL sameObjectAs(cap',
                h_val (hrs_mem \<acute>t_hrs) (cap_Ptr &(slot'\<rightarrow>[''cap_C'']))));;c)"
  apply (rule ccorres_gen_asm2)+
  apply (simp add: checkCapAt_def liftM_def bind_assoc del: Collect_const)
  apply (rule ccorres_symb_exec_l' [OF _ getCTE_inv getCTE_sp empty_fail_getCTE])
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule_tac xf'=ret__unsigned_long_' and val="from_bool (sameObjectAs cap (cteCap x))"
                and R="cte_wp_at' ((=) x) slot and valid_cap' cap and invs'"
                 in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
      apply (rule exI, rule conjI, assumption)
      apply (clarsimp simp: typ_heap_simps dest!: ccte_relation_ccap_relation)
      apply (rule exI, rule conjI, assumption)
      apply (auto intro: valid_capAligned dest: ctes_of_valid')[1]
     apply assumption
    apply (simp only: when_def if_to_top_of_bind)
    apply (rule ccorres_if_lhs)
     apply simp
    apply simp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemmas checkCapAt_ccorres2
    = checkCapAt_ccorres[where g=return, simplified bind_return]

lemma invs_psp_aligned_strg':
  "invs' s \<longrightarrow> pspace_aligned' s"
  by clarsimp

lemma cte_is_derived_capMasterCap_strg:
  "cte_wp_at' (is_derived' (ctes_of s) ptr cap \<circ> cteCap) ptr s
    \<longrightarrow> cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte) = capMasterCap cap \<or> P) ptr s"
  by (clarsimp simp: cte_wp_at_ctes_of is_derived'_def
                     badge_derived'_def)

lemma cteInsert_cap_to'2:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace>
     cteInsert newCap srcSlot destSlot
   \<lbrace>\<lambda>_. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteInsert_def ex_nonz_cap_to'_def setUntypedCapAsFull_def)
  apply (rule hoare_vcg_ex_lift)
  apply (wp updateMDB_weak_cte_wp_at
            updateCap_cte_wp_at_cases getCTE_wp' hoare_weak_lift_imp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply auto
  done

lemma threadSet_ipcbuffer_invs:
  "is_aligned a msg_align_bits \<Longrightarrow>
  \<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbIPCBuffer_update (\<lambda>_. a)) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)
  done

lemma canonical_address_bitfield_extract_tcb:
  "\<lbrakk>canonical_address t; is_aligned t tcbBlockSizeBits\<rbrakk> \<Longrightarrow>
     t = ctcb_ptr_to_tcb_ptr (tcb_Ptr (sign_extend 47 (ptr_val (tcb_ptr_to_ctcb_ptr t))))"
  apply (drule (1) canonical_address_tcb_ptr)
  by (fastforce simp: sign_extended_iff_sign_extend canonical_address_sign_extended)

lemma invokeTCB_ThreadControl_ccorres:
  notes prod.case_cong_weak[cong]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
   (invs' and sch_act_simple
          and tcb_inv_wf' (ThreadControl target slot faultep mcp priority cRoot vRoot buf)
          and (\<lambda>_. (faultep = None) = (cRoot = None) \<and> (cRoot = None) = (vRoot = None)
                    \<and> (case buf of Some (ptr, Some (cap, slot)) \<Rightarrow> slot \<noteq> 0 | _ \<Rightarrow> True)))
   (UNIV \<inter> {s. target_' s = tcb_ptr_to_ctcb_ptr target}
         \<inter> {s. (cRoot \<noteq> None \<or> buf \<noteq> None) \<longrightarrow> slot_' s = cte_Ptr slot}
         \<inter> {s. faultep_' s = option_to_0 faultep}
         \<inter> {s. mcp_' s = case_option 0 (ucast o fst) mcp}
         \<inter> {s. priority_' s = case_option 0 (ucast o fst) priority}
         \<inter> {s. case cRoot of None \<Rightarrow> True | Some (cRootCap, cRootSlot) \<Rightarrow> ccap_relation cRootCap (cRoot_newCap_' s)}
         \<inter> {s. cRoot_srcSlot_' s = cte_Ptr (option_to_0 (option_map snd cRoot))}
         \<inter> {s. case vRoot of None \<Rightarrow> True | Some (vRootCap, vRootSlot) \<Rightarrow> ccap_relation vRootCap (vRoot_newCap_' s)}
         \<inter> {s. vRoot_srcSlot_' s = cte_Ptr (option_to_0 (option_map snd vRoot))}
         \<inter> {s. bufferAddr_' s = option_to_0 (option_map fst buf)}
         \<inter> {s. bufferSrcSlot_' s = cte_Ptr (case buf of Some (ptr, Some (cap, slot)) \<Rightarrow> slot | _ \<Rightarrow> 0)}
         \<inter> {s. case buf of Some (ptr, Some (cap, slot)) \<Rightarrow> ccap_relation cap (bufferCap_' s) | _ \<Rightarrow> True}
         \<inter> {s. updateFlags_' s = (if mcp \<noteq> None then scast thread_control_update_mcp else 0)
                                  || (if priority \<noteq> None then scast thread_control_update_priority else 0)
                                  || (if buf \<noteq> None then scast thread_control_update_ipc_buffer else 0)
                                  || (if cRoot \<noteq> None then scast thread_control_update_space else 0)})
   []
   (invokeTCB (ThreadControl target slot faultep mcp priority cRoot vRoot buf))
   (Call invokeTCB_ThreadControl_'proc)"
    (is "ccorres ?rvr ?xf (?P and (\<lambda>_. ?P')) ?Q [] ?af ?cf")
  apply (rule ccorres_gen_asm)
  apply (cinit lift: target_' slot_' faultep_' mcp_' priority_' cRoot_newCap_' cRoot_srcSlot_'
                     vRoot_newCap_' vRoot_srcSlot_' bufferAddr_' bufferSrcSlot_' bufferCap_'
                     updateFlags_')
   apply csymbr
   apply (simp add: liftE_bindE case_option_If2 thread_control_flag_defs
                    word_ao_dist if_and_helper if_n_0_0 fun_app_def
                    tcb_cnode_index_defs[THEN ptr_add_assertion_positive[OF ptr_add_assertion_positive_helper]]
               del: Collect_const cong add: call_ignore_cong if_cong)
   apply (rule_tac P="ptr_val (tcb_ptr_to_ctcb_ptr target) && ~~ mask 5
                          = ptr_val (tcb_ptr_to_ctcb_ptr target)
                        \<and> ptr_val (tcb_ptr_to_ctcb_ptr target) && ~~ mask tcbBlockSizeBits = target
                        \<and> canonical_address target \<and> is_aligned target tcbBlockSizeBits"
                in ccorres_gen_asm)
   apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
       apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
         apply (simp add: Collect_const_mem)
        apply (rule ccorres_move_c_guard_tcb)
        apply (rule threadSet_ccorres_lemma2[where P=\<top>])
         apply vcg
        apply clarsimp
        apply (subst StateSpace.state.fold_congs[OF refl refl])
         apply (rule globals.fold_congs[OF refl refl])
         apply (rule heap_update_field_hrs)
           apply (simp add: typ_heap_simps)
          apply (fastforce intro: typ_heap_simps)
         apply simp
        apply (erule(1) rf_sr_tcb_update_no_queue2,
               (simp add: typ_heap_simps)+)
         apply (rule ball_tcb_cte_casesI, simp+)
        apply (clarsimp simp: ctcb_relation_def option_to_0_def)
       apply (rule ccorres_return_Skip)
      apply (rule ceqv_refl)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
         apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
           apply (simp add: Collect_const_mem)
          apply (ctac add: setMCPriority_ccorres)
         apply (rule ccorres_return_Skip)
        apply (rule ceqv_refl)
       apply (rule ccorres_subgoal_tailE)
        apply (rule ccorres_subgoal_tailE)
         apply (rule_tac A="invs' and sch_act_simple and tcb_at' target
                            and (\<lambda>(s::kernel_state). (case priority of None \<Rightarrow> True | Some x \<Rightarrow> ((\<lambda>y. fst y \<le> maxPriority)) x))
                            and case_option \<top> (case_option \<top> (valid_cap' \<circ> fst) \<circ> snd) buf
                            and case_option \<top> (case_option \<top> (cte_at' \<circ> snd) \<circ> snd) buf
                            and K (case_option True (swp is_aligned msg_align_bits \<circ> fst) buf)
                            and K (case_option True (case_option True (isArchObjectCap \<circ> fst) \<circ> snd) buf)"
                  (* bits of tcb_inv_wf' *)
                  in ccorres_guard_imp2[where A'=UNIV])
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp only: if_True Collect_True split_def bindE_assoc)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
           apply csymbr
           apply (simp add: liftE_bindE[symmetric] bindE_assoc getThreadBufferSlot_def
                            locateSlot_conv
                       del: Collect_const)
           apply (simp add: liftE_bindE del: Collect_const)
           apply (ctac(no_vcg) add: cteDelete_ccorres)
             apply (simp del: Collect_const add: Collect_False)
             apply (rule ccorres_move_c_guard_tcb)
             apply (rule ccorres_split_nothrow_novcg)
                 apply (rule threadSet_ccorres_lemma2[where P=\<top>])
                  apply vcg
                 apply clarsimp
                 apply (erule(1) rf_sr_tcb_update_no_queue2,
                        (simp add: typ_heap_simps')+, simp_all?)[1]
                  apply (rule ball_tcb_cte_casesI, simp+)
                 apply (clarsimp simp: ctcb_relation_def option_to_0_def)
                apply (rule ceqv_refl)
               apply csymbr
               apply (simp add: ccorres_cond_iffs Collect_False split_def
                           del: Collect_const)
               apply (rule ccorres_Cond_rhs_Seq)
                (* P *)
                apply (rule ccorres_rhs_assoc)+
                apply (simp add: case_option_If2 if_n_0_0 split_def
                            del: Collect_const)
                apply (rule checkCapAt_ccorres)
                   apply ceqv
                  apply csymbr
                  apply (simp add: Collect_True
                              del: Collect_const)
                  apply (rule ccorres_rhs_assoc)+
                  apply (rule checkCapAt_ccorres)
                     apply ceqv
                    apply csymbr
                    apply (simp add: Collect_True
                                del: Collect_const)
                    apply (simp add: assertDerived_def bind_assoc del: Collect_const)
                    apply (rule ccorres_symb_exec_l)
                       apply (ctac(no_vcg) add: cteInsert_ccorres)
                        apply (rule ccorres_pre_getCurThread)
                        apply (rule ccorres_split_nothrow_novcg_dc)
                           apply (simp add: when_def)
                           apply (rename_tac curThread)
                           apply (rule_tac C'="{s. target = curThread}"
                                           and Q="\<lambda>s. ksCurThread s = curThread"
                                           and Q'=UNIV in ccorres_rewrite_cond_sr)
                            apply (clarsimp simp: Collect_const_mem rf_sr_ksCurThread)
                           apply (rule ccorres_Cond_rhs; clarsimp)
                            apply (ctac (no_vcg) add: rescheduleRequired_ccorres)
                           apply (rule ccorres_return_Skip')
                          apply (rule ccorres_split_nothrow_novcg_dc)
                             apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
                              apply (ctac add: setPriority_ccorres)
                             apply (rule ccorres_return_Skip)
                            apply (rule ccorres_return_CE, simp+)[1]
                           apply (wp (once))
                          apply (clarsimp simp: guard_is_UNIV_def)
                         apply (wpsimp wp: when_def hoare_weak_lift_imp)
                          apply (strengthen sch_act_wf_weak, wp)
                         apply clarsimp
                         apply wp
                        apply (clarsimp simp : guard_is_UNIV_def Collect_const_mem)
                       apply (rule hoare_strengthen_post[
                                    where Q= "\<lambda>rv s.
                                              Invariants_H.valid_queues s \<and>
                                              valid_objs' s \<and>
                                              weak_sch_act_wf (ksSchedulerAction s) s \<and>
                                              ((\<exists>a b. priority = Some (a, b)) \<longrightarrow>
                                                   tcb_at' target s \<and> ksCurDomain s \<le> maxDomain \<and>
                                                   valid_queues' s \<and>  fst (the priority) \<le> maxPriority)"])
                        apply (strengthen sch_act_wf_weak)
                        apply (wp hoare_weak_lift_imp)
                       apply (clarsimp split: if_splits)
                      apply (wp empty_fail_stateAssert hoare_case_option_wp | simp del: Collect_const)+
                   apply csymbr
                   apply (simp add: Collect_False ccorres_cond_iffs
                               del: Collect_const)
                   apply (rule ccorres_pre_getCurThread)
                   apply (rename_tac curThread)
                   apply (rule ccorres_split_nothrow_novcg_dc)
                      apply (simp add: when_def)
                      apply (rule_tac C'="{s. target = curThread}"
                                      and Q="\<lambda>s. ksCurThread s = curThread"
                                      and Q'=UNIV in ccorres_rewrite_cond_sr)
                       apply (clarsimp simp: Collect_const_mem rf_sr_ksCurThread)
                      apply (rule ccorres_Cond_rhs; clarsimp)
                       apply (ctac (no_vcg) add: rescheduleRequired_ccorres)
                      apply (rule ccorres_return_Skip')
                     apply (rule ccorres_split_nothrow_novcg_dc)
                        apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
                         apply (ctac add: setPriority_ccorres)
                        apply (rule ccorres_return_Skip)
                       apply (rule ccorres_return_CE, simp+)
                      apply wp
                     apply (clarsimp simp: guard_is_UNIV_def)
                    apply (simp add: when_def)
                    apply (wp hoare_vcg_if_lift2(1) hoare_weak_lift_imp, strengthen sch_act_wf_weak; wp)
                   apply (clarsimp simp : guard_is_UNIV_def Collect_const_mem)
                  apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                                        tcbBuffer_def size_of_def cte_level_bits_def
                                        tcbIPCBufferSlot_def
                                        mask_def objBits_defs)
                 apply csymbr
                 apply (simp add: Collect_False ccorres_cond_iffs
                             del: Collect_const)
                 apply (rule ccorres_cond_false_seq, simp)
                 apply (rule ccorres_pre_getCurThread)
                 apply (rename_tac curThread)
                 apply (simp add: when_def)
                 apply (rule ccorres_split_nothrow_novcg_dc)
                    apply (rule_tac C'="{s. target = curThread}"
                                    and Q="\<lambda>s. ksCurThread s = curThread"
                                    and Q'=UNIV in ccorres_rewrite_cond_sr)
                     apply (clarsimp simp: Collect_const_mem rf_sr_ksCurThread)
                    apply (rule ccorres_Cond_rhs; clarsimp)
                     apply (ctac(no_vcg) add: rescheduleRequired_ccorres)
                    apply (rule ccorres_return_Skip')
                   apply (rule ccorres_split_nothrow_novcg_dc)
                      apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
                       apply (ctac add: setPriority_ccorres)
                      apply (rule ccorres_return_Skip)
                     apply (rule ccorres_return_CE, simp+)
                    apply wp
                   apply (clarsimp simp: guard_is_UNIV_def)
                  apply (wp hoare_vcg_if_lift2(1) hoare_weak_lift_imp, strengthen sch_act_wf_weak; wp)
                 apply (clarsimp simp : guard_is_UNIV_def Collect_const_mem)
                apply (simp add: guard_is_UNIV_def Collect_const_mem)
                apply (clarsimp simp: ccap_relation_def cap_thread_cap_lift cap_to_H_def canonical_address_bitfield_extract_tcb)
               (* \<not> P *)
               apply simp
               apply (rule ccorres_cond_false_seq, simp)
               apply (rule ccorres_cond_false_seq, simp)
               apply (simp split: option.split_asm)
               apply (rule ccorres_pre_getCurThread)
               apply (rename_tac curThread)
               apply (simp add: when_def)
               apply (rule ccorres_split_nothrow_novcg_dc)
                  apply (rule_tac C'="{s. target = curThread}"
                                  and Q="\<lambda>s. ksCurThread s = curThread"
                                  and Q'=UNIV in ccorres_rewrite_cond_sr)
                   apply (clarsimp simp: Collect_const_mem rf_sr_ksCurThread)
                  apply (rule ccorres_Cond_rhs; clarsimp)
                   apply (ctac(no_vcg) add: rescheduleRequired_ccorres)
                  apply (rule ccorres_return_Skip')
                 apply (rule ccorres_split_nothrow_novcg_dc)
                    apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
                     apply (ctac add: setPriority_ccorres)
                    apply (rule ccorres_return_Skip)
                   apply (rule ccorres_return_CE, simp+)
                  apply wp
                 apply (clarsimp simp: guard_is_UNIV_def)
                apply wpsimp
                 apply (wp hoare_weak_lift_imp, strengthen sch_act_wf_weak, wp )
                apply wp
               apply (clarsimp simp : guard_is_UNIV_def Collect_const_mem)
              apply (simp cong: conj_cong)
              apply (rule hoare_strengthen_post[
                            where Q="\<lambda>a b. (Invariants_H.valid_queues b \<and>
                                       valid_objs' b \<and>
                                       sch_act_wf (ksSchedulerAction b) b \<and>
                                       ((\<exists>a b. priority = Some (a, b)) \<longrightarrow>
                                          tcb_at'  target b \<and>
                                          ksCurDomain b \<le> maxDomain \<and> valid_queues' b \<and>
                                          fst (the priority) \<le> maxPriority)) \<and>
                                       ((case snd (the buf)
                                           of None \<Rightarrow> 0
                                            | Some x \<Rightarrow> snd x) \<noteq> 0 \<longrightarrow>
                                                invs' b \<and>
                                                valid_cap' (capability.ThreadCap target) b \<and>
                                                valid_cap' (fst (the (snd (the buf)))) b \<and>
                                                (cte_wp_at' (\<lambda>a. is_derived' (map_to_ctes (ksPSpace b))
                                                                 (snd (the (snd (the buf))))
                                                                 (fst (the (snd (the buf))))
                                                            (cteCap a)) (snd (the (snd (the buf)))) b \<longrightarrow>
                                                   cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte)
                                                                    = capMasterCap (fst (the (snd (the buf))))
                                                                    \<or> is_simple_cap' (fst (the (snd (the buf)))))
                                                               (snd (the (snd (the buf)))) b \<and>
                                                   valid_mdb' b \<and>
                                                   pspace_aligned' b \<and>
                                                   cte_wp_at' (\<lambda>c. True) (snd (the (snd (the buf)))) b))"])
               prefer 2
               apply fastforce
              apply (strengthen cte_is_derived_capMasterCap_strg
                                invs_queues invs_weak_sch_act_wf invs_sch_act_wf'
                                invs_valid_objs' invs_mdb' invs_pspace_aligned',
                            simp add: o_def)
              apply (rule_tac P="is_aligned (fst (the buf)) msg_align_bits"
                       in hoare_gen_asm)
              apply (wp threadSet_ipcbuffer_trivial hoare_weak_lift_imp
                     | simp
                     | strengthen invs_sch_act_wf' invs_valid_objs' invs_weak_sch_act_wf invs_queues
                                  invs_valid_queues' | wp hoare_drop_imps)+
             apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                                   option_to_0_def
                            split: option.split_asm)
            apply (clarsimp simp: ccap_relation_def cap_thread_cap_lift cap_to_H_def)
            apply (rule ccorres_split_throws)
             apply (rule ccorres_return_C_errorE, simp+)[1]
            apply vcg
           apply (simp add: conj_comms cong: conj_cong)
           apply (strengthen invs_ksCurDomain_maxDomain')
           apply (wp hoare_vcg_const_imp_lift_R cteDelete_invs')
          apply simp
          apply (rule ccorres_split_nothrow_novcg_dc)
             apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
              apply (ctac add: setPriority_ccorres)
             apply (rule ccorres_return_Skip)
            apply (rule ccorres_return_CE, simp+)
           apply wp
          apply (clarsimp simp: guard_is_UNIV_def)
         apply (clarsimp simp: inQ_def Collect_const_mem cintr_def
                               exception_defs tcb_cnode_index_defs)
         apply (simp add: tcbBuffer_def tcbIPCBufferSlot_def word_sle_def
                          cte_level_bits_def size_of_def case_option_If2 )
         apply (rule conjI)
          apply (clarsimp simp: objBits_simps' word_bits_conv case_option_If2 if_n_0_0 valid_cap'_def
                                capAligned_def obj_at'_def projectKOs)
         apply (clarsimp simp: invs_valid_objs' invs_valid_queues'
                               Invariants_H.invs_queues invs_ksCurDomain_maxDomain')
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
         apply (simp add: split_def getThreadVSpaceRoot_def locateSlot_conv
                          bindE_assoc liftE_bindE
                     del: Collect_const)
         apply csymbr
         apply (ctac(no_vcg) add: cteDelete_ccorres)
           apply (simp add: liftE_bindE Collect_False ccorres_cond_iffs
                       del: Collect_const)
           apply ((rule ccorres_split_nothrow_novcg_dc[rotated], assumption) | rule ccorres_rhs_assoc2)+
             apply (simp add: conj_comms pred_conj_def)
             apply (simp cong: conj_cong option.case_cong)
             apply (wp checked_insert_tcb_invs' hoare_case_option_wp
                       checkCap_inv [where P="tcb_at' p0" for p0]
                       checkCap_inv [where P="cte_at' p0" for p0]
                       checkCap_inv [where P="valid_cap' c" for c]
                       checkCap_inv [where P="sch_act_simple"]
                    | simp)+
            apply (simp add: guard_is_UNIV_def)
           apply (thin_tac "ccorres a1 a2 a3 a4 a5 a6 a7" for a1 a2 a3 a4 a5 a6 a7)
           apply (rule ccorres_rhs_assoc)+
           apply (rule checkCapAt_ccorres2)
              apply ceqv
             apply csymbr
             apply (simp add: Collect_True del: Collect_const)
             apply (rule ccorres_rhs_assoc)+
             apply (rule checkCapAt_ccorres2)
                apply ceqv
               apply csymbr
               apply (simp add: Collect_True assertDerived_def bind_assoc ccorres_cond_iffs
                           del: Collect_const)
               apply (rule ccorres_symb_exec_l)
                  apply (ctac add: cteInsert_ccorres)
                 apply (wp empty_fail_stateAssert hoare_case_option_wp | simp del: Collect_const)+
              apply csymbr
              apply (simp add: Collect_False ccorres_cond_iffs
                          del: Collect_const)
              apply (rule ccorres_return_Skip)
             apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                                   tcbVTable_def tcbVTableSlot_def Kernel_C.tcbVTable_def
                                   cte_level_bits_def size_of_def option_to_0_def objBits_defs mask_def)
            apply csymbr
            apply (simp add: Collect_False del: Collect_const)
            apply (rule ccorres_cond_false)
            apply (rule ccorres_return_Skip)
           apply (clarsimp simp: guard_is_UNIV_def ccap_relation_def cap_thread_cap_lift
                                 cap_to_H_def Collect_const_mem canonical_address_bitfield_extract_tcb)
          apply simp
          apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
          apply vcg
         apply (simp add: conj_comms, simp cong: conj_cong add: invs_mdb' invs_pspace_aligned')
         apply (simp add: cte_is_derived_capMasterCap_strg o_def)
         apply (wp cteDelete_invs' hoare_case_option_wp cteDelete_deletes
                   cteDelete_sch_act_simple
                | strengthen invs_valid_objs')+
         apply (rule hoare_post_imp_R[where Q' = "\<lambda>r. invs'"])
          apply (wp cteDelete_invs')
         apply (clarsimp simp:cte_wp_at_ctes_of)
        apply simp
       apply (rule ccorres_Cond_rhs_Seq)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
        apply (simp add: split_def getThreadCSpaceRoot_def locateSlot_conv
                         bindE_assoc liftE_bindE
                    del: Collect_const)
        apply csymbr
        apply (ctac(no_vcg) add: cteDelete_ccorres)
          apply (simp add: liftE_bindE Collect_False ccorres_cond_iffs
                      del: Collect_const)
          apply ((rule ccorres_split_nothrow_novcg_dc[rotated], assumption)
                  | rule ccorres_rhs_assoc2)+
            apply (simp add: conj_comms pred_conj_def)
            apply (simp cong: conj_cong option.case_cong)
            apply (wp checked_insert_tcb_invs' hoare_case_option_wp
                      checkCap_inv [where P="tcb_at' p0" for p0]
                      checkCap_inv [where P="cte_at' p0" for p0]
                      checkCap_inv [where P="valid_cap' c" for c]
                      checkCap_inv [where P="sch_act_simple"]
                   | simp)+
           apply (clarsimp simp: guard_is_UNIV_def word_sle_def Collect_const_mem
                                 option_to_0_def Kernel_C.tcbVTable_def tcbVTableSlot_def
                                 cte_level_bits_def size_of_def cintr_def
                                 tcb_cnode_index_defs objBits_defs mask_def)
          apply (thin_tac "ccorres a1 a2 a3 a4 a5 a6 a7" for a1 a2 a3 a4 a5 a6 a7)
          apply (rule ccorres_rhs_assoc)+
          apply (rule checkCapAt_ccorres2)
             apply ceqv
            apply csymbr
            apply (simp add: Collect_True del: Collect_const)
            apply (rule ccorres_rhs_assoc)+
            apply (rule checkCapAt_ccorres2)
               apply ceqv
              apply csymbr
              apply (simp add: Collect_True assertDerived_def bind_assoc ccorres_cond_iffs
                          del: Collect_const)
              apply (rule ccorres_symb_exec_l)
                 apply (ctac add: cteInsert_ccorres)
                apply (wp empty_fail_stateAssert  hoare_case_option_wp | simp del: Collect_const)+
             apply csymbr
             apply (simp add: Collect_False ccorres_cond_iffs
                         del: Collect_const)
             apply (rule ccorres_return_Skip)
            apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                                  Kernel_C.tcbCTable_def tcbCTableSlot_def if_1_0_0
                                  cte_level_bits_def size_of_def option_to_0_def mask_def objBits_defs)
           apply csymbr
           apply (simp add: Collect_False del: Collect_const)
           apply (rule ccorres_cond_false)
           apply (rule ccorres_return_Skip)
          apply (clarsimp simp: guard_is_UNIV_def ccap_relation_def cap_thread_cap_lift
                                cap_to_H_def Collect_const_mem canonical_address_bitfield_extract_tcb)
         apply simp
         apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
         apply vcg
        apply (simp add: conj_comms, simp cong: conj_cong add: invs_mdb' invs_pspace_aligned')
        apply (simp add: cte_is_derived_capMasterCap_strg o_def)
        apply (wp cteDelete_invs' hoare_case_option_wp cteDelete_deletes cteDelete_sch_act_simple
               | strengthen invs_valid_objs')+
        apply (rule hoare_post_imp_R[where Q' = "\<lambda>r. invs'"])
         apply (wp cteDelete_invs')
        apply (clarsimp simp:cte_wp_at_ctes_of)
       apply simp
      apply (simp add: conj_comms)
      apply (wp hoare_case_option_wp threadSet_invs_trivial setMCPriority_invs'
                typ_at_lifts[OF setMCPriority_typ_at']
                threadSet_cap_to' hoare_weak_lift_imp | simp)+
     apply (clarsimp simp: guard_is_UNIV_def tcbCTableSlot_def Kernel_C.tcbCTable_def
                           cte_level_bits_def size_of_def word_sle_def option_to_0_def
                           cintr_def objBits_defs mask_def)
    apply (simp add: conj_comms)
    apply (wp hoare_case_option_wp threadSet_invs_trivial
              threadSet_cap_to' hoare_weak_lift_imp | simp)+
   apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
  apply (clarsimp simp: inQ_def)
  apply (subst is_aligned_neg_mask_eq)
   apply (simp add: tcb_ptr_to_ctcb_ptr_def)
   apply (rule aligned_add_aligned)
     apply (fastforce simp add: obj_at'_def projectKOs objBits_simps')
    apply (simp add: ctcb_offset_defs is_aligned_def)
   apply (simp add: word_bits_conv)
  apply simp
  apply (subgoal_tac "s \<turnstile>' capability.ThreadCap target")
   apply (clarsimp simp: cte_level_bits_def Kernel_C.tcbCTable_def Kernel_C.tcbVTable_def
                         tcbCTableSlot_def tcbVTableSlot_def size_of_def
                         tcb_cte_cases_def isCap_simps tcb_aligned' obj_at'_is_canonical
                  split: option.split_asm
                  dest!: isValidVTableRootD invs_pspace_canonical')
  apply (clarsimp simp: valid_cap'_def capAligned_def word_bits_conv
                        obj_at'_def objBits_simps' projectKOs)
  done

lemma setupReplyMaster_ccorres:
  "ccorres dc xfdc (tcb_at' t)
        (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr t}) []
        (setupReplyMaster t) (Call setupReplyMaster_'proc)"
  apply (cinit lift: thread_')
   apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
   apply ctac
     apply (simp del: Collect_const)
     apply (rule ccorres_pre_getCTE)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule_tac F="\<lambda>rv'. (rv' = scast cap_null_cap) = (cteCap oldCTE = NullCap)"
                 and R="cte_wp_at' ((=) oldCTE) rv"
               and xf'=ret__unsigned_longlong_'
                  in ccorres_symb_exec_r_abstract_UNIV[where R'=UNIV])
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
        apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap
                       dest!: ccte_relation_ccap_relation)
       apply ceqv
      apply (simp only:)
      apply (rule ccorres_when[where R=\<top>])
       apply (simp add: Collect_const_mem)
      apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_stateAssert])
        apply (rule_tac P="cte_at' rv and tcb_at' t" in ccorres_from_vcg[where P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
        apply (rule conjI, fastforce intro: typ_heap_simps)
        apply (clarsimp simp: typ_heap_simps)
        apply (rule fst_setCTE[OF ctes_of_cte_at], assumption)
        apply (rule rev_bexI, assumption)
        apply (clarsimp simp: rf_sr_def cstate_relation_def
                              cpspace_relation_def Let_def
                              typ_heap_simps')
        apply (subst setCTE_tcb_case, assumption+)
        apply (rule_tac r="s'" in KernelStateData_H.kernel_state.cases)
        apply clarsimp
        apply (rule conjI)
         apply (erule(2) cmap_relation_updI)
          apply (clarsimp simp: ccte_relation_def cap_reply_cap_lift cte_lift_def
                                cong: option.case_cong_weak)
          apply (simp add: cte_to_H_def cap_to_H_def mdb_node_to_H_def
                           nullMDBNode_def c_valid_cte_def)
          apply (simp add: cap_reply_cap_lift)
         apply simp
        apply (simp add: cmachine_state_relation_def packed_heap_update_collapse_hrs
                         carch_state_relation_def carch_globals_def
                         fpu_null_state_heap_update_tag_disj_simps
                         global_ioport_bitmap_heap_update_tag_disj_simps
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
       apply (wp | simp)+
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (wp | simp add: locateSlot_conv)+
   apply vcg
  apply (clarsimp simp: word_sle_def cte_wp_at_ctes_of
                        tcb_cnode_index_defs tcbReplySlot_def)
  done

lemma restart_ccorres:
  "ccorres dc xfdc (invs' and tcb_at' thread and sch_act_simple)
        (UNIV \<inter> {s. target_' s = tcb_ptr_to_ctcb_ptr thread}) []
     (restart thread) (Call restart_'proc)"
  apply (cinit lift: target_')
   apply (ctac(no_vcg) add: isStopped_ccorres)
    apply (simp only: when_def)
    apply (rule ccorres_cond2[where R=\<top>])
      apply (simp add: to_bool_def Collect_const_mem)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac(no_vcg) add: cancelIPC_ccorres1[OF cteDeleteOne_ccorres])
      apply (ctac(no_vcg) add: setupReplyMaster_ccorres)
       apply (ctac(no_vcg))
        apply (ctac(no_vcg) add: tcbSchedEnqueue_ccorres)
         apply (ctac add: possibleSwitchTo_ccorres)
        apply (wp weak_sch_act_wf_lift)[1]
       apply (wp sts_valid_queues setThreadState_st_tcb)[1]
      apply (simp add: valid_tcb_state'_def)
      apply wp
      apply (wp (once) sch_act_wf_lift, (wp tcb_in_cur_domain'_lift)+)
     apply (rule hoare_strengthen_post)
      apply (rule hoare_vcg_conj_lift)
       apply (rule delete_one_conc_fr.cancelIPC_invs)

      apply (rule cancelIPC_tcb_at'[where t=thread])
     apply fastforce
    apply (rule ccorres_return_Skip)
   apply (wp hoare_drop_imps)
  apply (auto simp: Collect_const_mem mask_def ThreadState_defs)
  done

lemma setNextPC_ccorres:
  "ccorres dc xfdc \<top>
       (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
             \<inter> {s. v_' s = val}) []
       (asUser thread (setNextPC val))
       (Call setNextPC_'proc)"
  apply (cinit')
   apply (simp add: setNextPC_def)
   apply (ctac add: setRegister_ccorres)
  apply simp
  done

lemma Arch_performTransfer_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
            \<top> UNIV []
       (liftE (performTransfer a b c))
       (Call Arch_performTransfer_'proc)"
  apply (cinit' simp: performTransfer_def)
   apply (fold returnOk_liftE)
   apply (rule ccorres_return_CE)
     apply simp+
  done

(*FIXME: arch_split: C kernel names hidden by Haskell names *)
abbreviation "frameRegistersC \<equiv> kernel_all_substitute.frameRegisters"
lemmas frameRegistersC_def = kernel_all_substitute.frameRegisters_def
abbreviation "gpRegistersC \<equiv> kernel_all_substitute.gpRegisters"
lemmas gpRegistersC_def = kernel_all_substitute.gpRegisters_def

lemma frame_gp_registers_convs:
  "length X64_H.frameRegisters = unat n_frameRegisters"
  "length X64_H.gpRegisters = unat n_gpRegisters"
  "n < length X64_H.frameRegisters \<Longrightarrow>
     index frameRegistersC n = register_from_H (X64_H.frameRegisters ! n)"
  "n < length X64_H.gpRegisters \<Longrightarrow>
     index gpRegistersC n = register_from_H (X64_H.gpRegisters ! n)"
  apply (simp_all add: X64_H.gpRegisters_def X64_H.frameRegisters_def
                       X64.gpRegisters_def n_gpRegisters_def
                       X64.frameRegisters_def n_frameRegisters_def
                       frameRegistersC_def gpRegistersC_def msgRegisters_unfold
                       fupdate_def Arrays.update_def toEnum_def
                       upto_enum_def fromEnum_def enum_register)
  apply (auto simp: less_Suc_eq)
  done


lemma postModifyRegisters_ccorres:
  "ccorres dc xfdc
      (\<lambda>s. ct = ksCurThread s)
      \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr dest\<rbrace> hs
      (asUser dest (postModifyRegisters ct dest))
      (Call Arch_postModifyRegisters_'proc)"
  supply if_cong[cong]
  apply (cinit' lift: tptr_')
   apply (rule_tac xf'' = xfdc and
                      A = "(\<lambda>s. ct = ksCurThread s)" and
                      C'= "UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr dest}"
              in ccorres_call[rotated])
      apply (simp+)[3]
   apply (cinit' lift: tptr_' simp: postModifyRegisters_def when_def)
    apply (simp add: if_distrib[where f="asUser t" for t] asUser_return)
    apply (rule_tac R="\<lambda>s. ct = ksCurThread s" in ccorres_cond2)
      apply (clarsimp simp: rf_sr_ksCurThread)
     apply (ctac add: setRegister_ccorres)
    apply (rule ccorres_add_return2)
    apply (rule ccorres_stateAssert)
    apply (rule ccorres_return_Skip')
   by simp+

lemma invokeTCB_CopyRegisters_ccorres:
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
   (invs' and sch_act_simple and tcb_at' destn and tcb_at' source
          and ex_nonz_cap_to' destn and ex_nonz_cap_to' source)
   (UNIV \<inter> {s. dest___ptr_to_struct_tcb_C_' s = tcb_ptr_to_ctcb_ptr destn}
         \<inter> {s. tcb_src_' s = tcb_ptr_to_ctcb_ptr source}
         \<inter> {s. to_bool (resumeTarget_' s) = resume}
         \<inter> {s. to_bool (suspendSource_' s) = susp}
         \<inter> {s. to_bool (transferFrame_' s) = frames}
         \<inter> {s. to_bool (transferInteger_' s) = ints}) []
   (invokeTCB (CopyRegisters destn source susp resume frames ints arch))
   (Call invokeTCB_CopyRegisters_'proc)"
  apply (cinit lift: dest___ptr_to_struct_tcb_C_' tcb_src_' resumeTarget_'
                     suspendSource_' transferFrame_' transferInteger_'
               simp: whileAnno_def)
   apply (simp add: liftE_def bind_assoc whileAnno_def
               del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule ccorres_when[where R=\<top>])
       apply (simp add: to_bool_def del: Collect_const)
      apply (ctac add: suspend_ccorres[OF cteDeleteOne_ccorres])
     apply (rule ccorres_split_nothrow_novcg_dc)
        apply (rule ccorres_when[where R=\<top>])
         apply (simp add: to_bool_def del: Collect_const)
        apply (ctac add: restart_ccorres)
       apply (rule ccorres_split_nothrow_novcg_dc)
          apply (rule ccorres_when[where R=\<top>])
           apply (simp add: to_bool_def Collect_const_mem)
          apply (rule ccorres_rhs_assoc)+
          apply (csymbr, csymbr, csymbr)
          apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg_dc)
             apply (rule ccorres_rel_imp)
              apply (rule ccorres_mapM_x_while[where F="\<lambda>x. tcb_at' destn and tcb_at' source"])
                  apply clarsimp
                  apply (rule ccorres_guard_imp2)
                   apply (ctac(no_vcg) add: getRegister_ccorres)
                    apply (ctac add: setRegister_ccorres)
                   apply wp
                  apply (clarsimp simp: frame_gp_registers_convs
                                        n_frameRegisters_def unat_of_nat64
                                        word_bits_def word_of_nat_less)
                 apply (simp add: frame_gp_registers_convs n_frameRegisters_def)
                apply (rule allI, rule conseqPre, vcg)
                apply clarsimp
               apply (wp | simp)+
              apply (simp add: frame_gp_registers_convs n_frameRegisters_def
                               word_bits_def)
             apply simp
            apply (ctac(no_vcg) add: getRestartPC_ccorres)
             apply (ctac add: setNextPC_ccorres)
            apply wp+
          apply (clarsimp simp: guard_is_UNIV_def)
         apply (rule ccorres_split_nothrow_novcg_dc)
            apply (rule ccorres_when[where R=\<top>])
             apply (simp add: to_bool_def Collect_const_mem)
            apply (rule ccorres_rhs_assoc)+
            apply (csymbr, csymbr)
            apply (rule ccorres_rel_imp)
             apply (rule ccorres_mapM_x_while[where F="\<lambda>x. tcb_at' destn and tcb_at' source"])
                 apply clarsimp
                 apply (rule ccorres_guard_imp2)
                  apply ((wp | ctac(no_vcg) add: getRegister_ccorres setRegister_ccorres)+)[1]
                 apply (clarsimp simp: frame_gp_registers_convs n_gpRegisters_def
                                       unat_of_nat64 word_bits_def word_of_nat_less)
                apply (simp add: frame_gp_registers_convs n_gpRegisters_def)
               apply (rule allI, rule conseqPre, vcg)
               apply clarsimp
              apply (wp | simp)+
             apply (simp add: word_bits_def frame_gp_registers_convs n_gpRegisters_def)
            apply simp
           apply (rule ccorres_pre_getCurThread)
           apply (ctac add: postModifyRegisters_ccorres)
             apply (rule ccorres_split_nothrow_novcg_dc)
                apply (rule_tac R="\<lambda>s. rvc = ksCurThread s"
                           in ccorres_when)
                 apply (clarsimp simp: rf_sr_ksCurThread)
                apply clarsimp
                apply (ctac (no_vcg) add: rescheduleRequired_ccorres)
               apply (simp only: liftE_bindE[symmetric] return_returnOk)
               apply (ctac(no_vcg) add: Arch_performTransfer_ccorres)
                 apply (rule ccorres_return_CE, simp+)[1]
                apply (rule ccorres_return_C_errorE, simp+)[1]
               apply simp
               apply wp+
             apply (clarsimp simp: guard_is_UNIV_def)
            apply simp
            apply (wpsimp simp: postModifyRegisters_def pred_conj_def
                          cong: if_cong
                            wp: hoare_drop_imp)
           apply vcg
          apply (simp add: pred_conj_def guard_is_UNIV_def cong: if_cong
                  | wp mapM_x_wp_inv hoare_drop_imp)+
      apply clarsimp
      apply (rule_tac Q="\<lambda>rv. invs' and tcb_at' destn" in hoare_strengthen_post[rotated])
       apply (fastforce simp: sch_act_wf_weak)
      apply (wpsimp wp: hoare_drop_imp restart_invs')+
     apply (clarsimp simp add: guard_is_UNIV_def)
    apply (wp hoare_drop_imp hoare_vcg_if_lift)+
    apply simp
    apply (rule_tac Q="\<lambda>rv. invs' and tcb_at' destn" in hoare_strengthen_post[rotated])
     apply (fastforce simp: sch_act_wf_weak)
    apply (wpsimp wp: hoare_drop_imp)+
   apply (clarsimp simp add: guard_is_UNIV_def)
  apply (clarsimp simp: invs_weak_sch_act_wf invs_valid_objs'
                 split: if_split cong: if_cong | rule conjI)+
     apply (clarsimp dest!: global'_no_ex_cap simp: invs'_def valid_state'_def | rule conjI)+
  done

lemma invokeTCB_WriteRegisters_ccorres_helper:
  "\<lbrakk> unat (f (of_nat n)) = incn
         \<and> g (of_nat n) = register_from_H reg \<and> n'=incn
         \<and> of_nat n < bnd \<and> of_nat n < bnd2 \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc (sysargs_rel args buffer and sysargs_rel_n args buffer n' and
                    tcb_at' dst and P)
                   (\<lbrace>\<acute>i = of_nat n\<rbrace>) hs
     (asUser dst (setRegister reg
          (sanitiseRegister t reg (args ! incn))))
     (\<acute>ret__unsigned_long :== CALL getSyscallArg(f (\<acute>i),option_to_ptr buffer);;
      Guard ArrayBounds \<lbrace>\<acute>i < bnd\<rbrace>
          (\<acute>unsigned_long_eret_2 :== CALL sanitiseRegister(g (\<acute>i),\<acute>ret__unsigned_long,from_bool t));;
      Guard ArrayBounds \<lbrace>\<acute>i < bnd2\<rbrace>
        (CALL setRegister(tcb_ptr_to_ctcb_ptr dst,g (\<acute>i),\<acute>unsigned_long_eret_2)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return)
   apply (rule ccorres_rhs_assoc)+
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n="incn" and buffer=buffer])
     apply (rule ccorres_symb_exec_r)
       apply (ctac add: setRegister_ccorres)
      apply (vcg)
     apply clarsimp
     apply (rule conseqPre, vcg, clarsimp)
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply fastforce
  done

lemma doMachineOp_context:
  "(rv,s') \<in> fst (doMachineOp f s) \<Longrightarrow>
  (rv,s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbContext_update (\<lambda>_. st) ko))\<rparr>)
  \<in> fst (doMachineOp f (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbContext_update (\<lambda>_. st) ko))\<rparr>))"
  apply (clarsimp simp: doMachineOp_def split_def in_monad select_f_def)
  apply fastforce
  done


lemma getObject_context:
  " \<lbrakk>(x, s') \<in> fst (getObject t' s); ko_at' ko t s\<rbrakk>
  \<Longrightarrow> (if t = t' then tcbContext_update (\<lambda>_. st) x else x,
      s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbContext_update (\<lambda>_. st) ko))\<rparr>)
      \<in> fst (getObject t' (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbContext_update (\<lambda>_. st) ko))\<rparr>))"
  apply (simp split: if_split)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: getObject_def split_def loadObject_default_def in_monad
                         Corres_C.in_magnitude_check' projectKOs objBits_simps')
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs objBits_simps)
   apply (simp add: magnitudeCheck_def in_monad split: option.splits)
   apply clarsimp
   apply (simp add: lookupAround2_char2)
   apply (clarsimp split: if_split_asm)
   apply (erule_tac x=x2 in allE)
   apply (clarsimp simp: ps_clear_def)
   apply (drule_tac x=x2 in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply simp
   apply (erule notE, rule word_diff_ls'(3))
    apply unat_arith
   apply (drule is_aligned_no_overflow)
   apply simp
  apply clarsimp
  apply (clarsimp simp: getObject_def split_def loadObject_default_def in_monad
                        Corres_C.in_magnitude_check' projectKOs objBits_simps')
  apply (simp add: magnitudeCheck_def in_monad split: option.splits)
  apply clarsimp
  apply (simp add: lookupAround2_char2)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x=t in allE)
   apply simp
   apply (clarsimp simp: obj_at'_real_def projectKOs
                         ko_wp_at'_def objBits_simps)
   apply (simp add: ps_clear_def)
   apply (drule_tac x=t in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply simp
   apply (erule notE, rule word_diff_ls'(3))
    apply unat_arith
   apply (drule is_aligned_no_overflow)
   apply simp
  apply (erule_tac x=x2 in allE)
  apply (clarsimp simp: ps_clear_def)
  apply (drule_tac x=x2 in orthD2)
   apply fastforce
  apply clarsimp
  apply (erule impE)
   apply (rule word_diff_ls'(3))
   apply unat_arith
   apply (drule is_aligned_no_overflow)
   apply simp
  apply fastforce
  done

lemma threadGet_context:
  "\<lbrakk> (uc, s') \<in> fst (threadGet (atcbContextGet o tcbArch) (ksCurThread s) s); ko_at' ko t s;
      t \<noteq> ksCurThread s \<rbrakk> \<Longrightarrow>
   (uc, s'\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbArch_update (\<lambda>_. atcbContextSet st (tcbArch ko)) ko))\<rparr>) \<in>
  fst (threadGet (atcbContextGet o tcbArch) (ksCurThread s) (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbArch_update (\<lambda>_. atcbContextSet st (tcbArch ko)) ko))\<rparr>))"
  apply (clarsimp simp: threadGet_def liftM_def in_monad)
  apply (drule (1) getObject_context [where st=st])
  apply (rule exI)
  apply (erule conjI)
  apply (simp split: if_splits)
done


lemma asUser_context:
  "\<lbrakk>(x,s) \<in> fst (asUser (ksCurThread s) f s); ko_at' ko t s; \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace> ;
    t \<noteq> ksCurThread s\<rbrakk> \<Longrightarrow>
  (x,s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbArch_update (\<lambda>_. atcbContextSet st (tcbArch ko)) ko))\<rparr>) \<in>
  fst (asUser (ksCurThread s) f (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbArch_update (\<lambda>_. atcbContextSet st (tcbArch ko)) ko))\<rparr>))"
  apply (clarsimp simp: asUser_def in_monad select_f_def)
  apply (frule use_valid, rule threadGet_inv [where P="(=) s"], rule refl)
  apply (frule use_valid, assumption, rule refl)
  apply clarsimp
  apply (frule (2) threadGet_context)
  apply (intro exI)
  apply (erule conjI)
  apply (rule exI, erule conjI)
  apply (clarsimp simp: threadSet_def in_monad)
  apply (frule use_valid, rule getObject_inv [where P="(=) s"])
    apply (simp add: loadObject_default_def)
    apply wp
    apply simp
   apply (rule refl)
  apply clarsimp
  apply (frule (1) getObject_context)
  apply (intro exI)
  apply (erule conjI)
  apply (clarsimp simp: setObject_def split_def updateObject_default_def threadGet_def
                        Corres_C.in_magnitude_check' getObject_def loadObject_default_def liftM_def
                        objBits_simps' projectKOs in_monad)

  apply (clarsimp simp: magnitudeCheck_def in_monad split: option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (cases s, simp)
   apply (rule ext, clarsimp split: if_split)
   apply (case_tac tcb, simp)

  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp add: lookupAround2_char2 split: if_split_asm)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs objBits_simps)
    apply (erule_tac x=t in allE)
    apply simp
    apply (simp add: ps_clear_def)
    apply (drule_tac x=t in orthD2)
     apply fastforce
    apply clarsimp
    apply (erule impE, simp)
    apply (erule notE, rule word_diff_ls'(3))
     apply unat_arith
    apply (drule is_aligned_no_overflow)
    apply simp
   apply (erule_tac x=x2 in allE)
   apply simp
   apply (simp add: ps_clear_def)
   apply (drule_tac x=x2 in orthD2)
    apply fastforce
   apply clarsimp
   apply (erule impE)
    apply (rule word_diff_ls'(3))
     apply unat_arith
    apply (drule is_aligned_no_overflow)
    apply simp
   apply (erule impE, simp)
   apply simp
  apply (rule exI)
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (cases s, clarsimp)
  apply (rule ext, clarsimp split: if_split)
  apply (case_tac tcb, clarsimp)
done


lemma getMRs_rel_context:
  "\<lbrakk>getMRs_rel args buffer s;
    (cur_tcb' and case_option \<top> valid_ipc_buffer_ptr' buffer) s;
    ko_at' ko t s ; t \<noteq> ksCurThread s\<rbrakk> \<Longrightarrow>
  getMRs_rel args buffer (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> KOTCB (tcbArch_update (\<lambda>_. atcbContextSet st (tcbArch ko)) ko))\<rparr>)"
  apply (clarsimp simp: getMRs_rel_def)
  apply (rule exI, erule conjI)
  apply (subst (asm) det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def)
  apply (subst det_wp_use, rule det_wp_getMRs)
   apply (simp add: cur_tcb'_def)
   apply (rule conjI)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs
                          objBits_simps ps_clear_def split: if_split)
   apply (clarsimp simp: valid_ipc_buffer_ptr'_def split: option.splits)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def projectKOs obj_at'_real_def
                         objBits_simps ps_clear_def split: if_split)
  apply (clarsimp simp: getMRs_def in_monad)
  apply (frule use_valid, rule asUser_inv [where P="(=) s"])
    apply (wp mapM_wp' getRegister_inv)[1]
   apply simp
  apply clarsimp
  apply (drule (1) asUser_context)
    apply (wp mapM_wp' getRegister_inv)[1]
   apply assumption
  apply (intro exI)
  apply (erule conjI)
  apply (cases buffer)
   apply (clarsimp simp: return_def)
  apply clarsimp
  apply (drule mapM_upd_inv [rotated -1])
    prefer 3
    apply fastforce
   prefer 2
   apply wp
  apply (clarsimp simp: loadWordUser_def in_monad stateAssert_def word_size
                  simp del: fun_upd_apply)
  apply (rule conjI)
   apply (clarsimp simp: pointerInUserData_def typ_at'_def ko_wp_at'_def
                         projectKOs ps_clear_def obj_at'_real_def
                  split: if_split)
  apply (erule doMachineOp_context)
done

lemma asUser_getMRs_rel:
  "\<lbrace>(\<lambda>s. t \<noteq> ksCurThread s) and getMRs_rel args buffer and cur_tcb'
        and case_option \<top> valid_ipc_buffer_ptr' buffer \<rbrace>
  asUser t f \<lbrace>\<lambda>_. getMRs_rel args buffer\<rbrace>"
  apply (simp add: asUser_def)
  apply (rule hoare_pre, wp)
     apply (simp add: threadSet_def)
     apply (simp add: setObject_def split_def updateObject_default_def)
     apply wp
     apply (simp del: fun_upd_apply)
     apply (wp getObject_tcb_wp)
   apply (wp threadGet_wp)+
  apply (clarsimp simp del: fun_upd_apply)
  apply (drule obj_at_ko_at')+
  apply (clarsimp simp del: fun_upd_apply)
  apply (rule exI, rule conjI, assumption)
  apply (clarsimp split: if_split simp del: fun_upd_apply)
  apply (erule getMRs_rel_context, simp)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs)
  apply simp
  done


lemma asUser_sysargs_rel:
  "\<lbrace>\<lambda>s. t \<noteq> ksCurThread s \<and> sysargs_rel args buffer s\<rbrace>
  asUser t f \<lbrace>\<lambda>_. sysargs_rel args buffer\<rbrace>"
  apply (cases buffer, simp_all add: sysargs_rel_def)
   apply (rule hoare_pre)
   apply (wp asUser_getMRs_rel hoare_valid_ipc_buffer_ptr_typ_at'|simp)+
done

lemma threadSet_same:
  "\<lbrace>\<lambda>s. \<exists>tcb'. ko_at' tcb' t s \<and> tcb = f tcb'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. ko_at' tcb t\<rbrace>"
  unfolding threadSet_def
  by (wpsimp wp: setObject_tcb_strongest getObject_tcb_wp) fastforce

lemma asUser_setRegister_ko_at':
  "\<lbrace>obj_at' (\<lambda>tcb'. tcb = tcbArch_update (\<lambda>_. atcbContextSet (modify_registers (\<lambda>regs. regs(r := v)) (atcbContextGet (tcbArch tcb'))) (tcbArch tcb')) tcb') dst\<rbrace>
  asUser dst (setRegister r v) \<lbrace>\<lambda>rv. ko_at' (tcb::tcb) dst\<rbrace>"
  unfolding asUser_def
  apply (wpsimp wp: threadSet_same threadGet_wp)
  apply (clarsimp simp: setRegister_def simpler_modify_def obj_at'_def modify_registers_def)
  done

lemma invokeTCB_WriteRegisters_ccorres[where S=UNIV]:
  notes hoare_weak_lift_imp [wp] word_less_1[simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
   (invs' and tcb_at' dst and ex_nonz_cap_to' dst and sch_act_simple
          and sysargs_rel args buffer
          and (\<lambda>s. dst \<noteq> ksCurThread s)
          and (\<lambda>_. values = take someNum (drop 2 args)
                   \<and> someNum + 2 \<le> length args))
   ({s. unat (n_' s) = length values} \<inter> S
         \<inter> {s. unat (n_' s) = length values}
         \<inter> {s. dest___ptr_to_struct_tcb_C_' s = tcb_ptr_to_ctcb_ptr dst}
         \<inter> {s. resumeTarget_' s = from_bool resume}
         \<inter> {s. buffer_' s = option_to_ptr buffer}) []
   (invokeTCB (WriteRegisters dst resume values arch))
   (Call invokeTCB_WriteRegisters_'proc)"
  supply empty_fail_cond[simp]
  apply (rule ccorres_gen_asm)
  apply (erule conjE)
  apply (cinit lift: n_' dest___ptr_to_struct_tcb_C_' resumeTarget_' buffer_'
               simp: whileAnno_def)
   (* using S not univ seems to stop cinit doing this? *)
   apply (csymbr, csymbr, csymbr, csymbr)
   apply (simp add: liftE_def bind_assoc
               del: Collect_const)
   apply (rule ccorres_pre_getCurThread)
   apply (rule_tac P="\<lambda>a. ccorres_underlying rf_sr \<Gamma> r' xf arrel axf P P' hs a c" for r' xf arrel axf P P' hs c in subst)
    apply (rule liftE_bindE)

   apply (ctac add: Arch_performTransfer_ccorres)
      apply (simp add: Collect_False whileAnno_def del: Collect_const)
      apply (rule ccorres_add_return)
      apply (rule_tac xf'=n_' and r'="\<lambda>rv rv'. rv' = min n (scast n_frameRegisters + scast n_gpRegisters)"
                   in ccorres_split_nothrow)
          apply (rule_tac P'="{s. n_' s = n}" in ccorres_from_vcg[where P=\<top>])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: return_def min_def)
          apply (simp add: linorder_not_less[symmetric] n_gpRegisters_def n_frameRegisters_def)
         apply ceqv
        apply (ctac add: Arch_getSanitiseRegisterInfo_ccorres)
          apply (simp add: zipWithM_mapM split_def zip_append1 mapM_discarded mapM_x_append
                      del: Collect_const)
          apply (simp add: asUser_bind_distrib getRestartPC_def setNextPC_def bind_assoc
                      del: Collect_const)
          apply (simp only: getRestartPC_def[symmetric] setNextPC_def[symmetric])
          apply (simp add: asUser_mapM_x bind_assoc)
          apply (rule ccorres_stateAssert)
          apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg)
              apply (drule_tac t="archInfo" in sym, simp only:)
              apply (rule_tac F="\<lambda>n. sysargs_rel args buffer and sysargs_rel_n args buffer (n + 2) and
                                     tcb_at' dst and (\<lambda>s. dst \<noteq> ksCurThread s)"
                          and Q=UNIV in ccorres_mapM_x_whileQ)
                  apply clarsimp
                  apply (rule invokeTCB_WriteRegisters_ccorres_helper [where args=args])
                  apply (simp add: unat_word_ariths frame_gp_registers_convs n_frameRegisters_def
                                   unat_of_nat64 word_bits_def word_of_nat_less)
                 apply (simp add: n_frameRegisters_def n_gpRegisters_def
                                  frame_gp_registers_convs word_less_nat_alt)
                 apply (simp add: unat_of_nat64 word_bits_def)
                 apply arith
                apply clarsimp
                apply (vcg exspec=setRegister_modifies exspec=getSyscallArg_modifies
                           exspec=sanitiseRegister_modifies)
                apply clarsimp
               apply (simp add: sysargs_rel_n_def)
               apply (rule hoare_pre, wp asUser_sysargs_rel asUser_setRegister_ko_at')
               apply (clarsimp simp: n_msgRegisters_def sysargs_rel_def)
              apply (simp add: frame_gp_registers_convs n_frameRegisters_def word_bits_def)
             apply simp
             apply (rule ceqv_refl)
            apply (rule ccorres_stateAssert)
            apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg)
                apply (drule_tac t="archInfo" in sym, simp only:)
                apply (rule_tac F="\<lambda>n. sysargs_rel args buffer
                                     and sysargs_rel_n args buffer (n + length X64_H.frameRegisters + 2)
                                     and tcb_at' dst and (\<lambda>s. dst \<noteq> ksCurThread s)"
                                     and Q=UNIV in ccorres_mapM_x_whileQ)
                    apply clarsimp
                    apply (rule invokeTCB_WriteRegisters_ccorres_helper [where args=args])
                    apply (simp add: n_gpRegisters_def unat_word_ariths
                                     frame_gp_registers_convs unat_of_nat64
                                     word_bits_def n_frameRegisters_def
                                     word_of_nat_less word_less_1)
                   apply (simp add: n_frameRegisters_def n_gpRegisters_def
                                    frame_gp_registers_convs unat_of_nat64
                                    word_less_nat_alt word_bits_def
                                    less_diff_conv)
                   apply (simp add: unat_word_ariths cong: conj_cong)
                  apply clarsimp
                  apply (vcg exspec=setRegister_modifies exspec=getSyscallArg_modifies
                             exspec=sanitiseRegister_modifies)
                  apply clarsimp
                 apply (simp add: sysargs_rel_n_def)
                 apply (rule hoare_pre, wp asUser_sysargs_rel)
                 apply (clarsimp simp: n_msgRegisters_def frame_gp_registers_convs
                                       n_frameRegisters_def)
                 apply arith
                apply (simp add: X64_H.gpRegisters_def word_bits_def
                                 X64.gpRegisters_def)
               apply simp
               apply (rule ceqv_refl)
              apply (ctac(no_vcg) add: getRestartPC_ccorres)
               apply simp
               apply (ctac(no_vcg) add: setNextPC_ccorres)
                apply (ctac (no_vcg) add: postModifyRegisters_ccorres)
                 apply (rule ccorres_split_nothrow_novcg)
                     apply (rule ccorres_when[where R=\<top>])
                      apply (simp add: from_bool_0 Collect_const_mem)
                     apply (rule_tac xf'=Corres_C.xfdc in ccorres_call)
                        apply (rule restart_ccorres)
                       apply simp
                      apply simp
                     apply simp
                    apply (rule ceqv_refl)
                   apply (rule ccorres_split_nothrow_novcg_dc)
                      apply (rule_tac R="\<lambda>s. self = ksCurThread s"
                                  in ccorres_when)
                      apply (clarsimp simp: rf_sr_ksCurThread)
                      apply clarsimp
                      apply (ctac (no_vcg) add: rescheduleRequired_ccorres)
                     apply (unfold return_returnOk)[1]
                     apply (rule ccorres_return_CE, simp+)[1]
                    apply wp
                   apply (simp add: guard_is_UNIV_def)
                  apply (wp hoare_drop_imp)
                   apply (rule_tac Q="\<lambda>rv. invs' and tcb_at' dst" in hoare_strengthen_post[rotated])
                    apply (fastforce simp: sch_act_wf_weak)
                   apply (wpsimp wp: restart_invs')+
                 apply (clarsimp simp add: guard_is_UNIV_def)
                apply (wp hoare_drop_imp hoare_vcg_if_lift)+
             apply simp
             apply (rule mapM_x_wp')
             apply (wpsimp)
            apply (simp add: guard_is_UNIV_def)
           apply (rule hoare_drop_imps)
           apply (simp add: sysargs_rel_n_def)
           apply (wp mapM_x_wp')
            apply (rule hoare_pre, wp asUser_sysargs_rel)
            apply clarsimp
           apply wpsimp
          apply (simp add: guard_is_UNIV_def)
         apply (wp)
        apply vcg
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
     apply simp
    apply (simp add: performTransfer_def)
    apply wp
   apply clarsimp
   apply vcg
  apply (clarsimp simp: n_msgRegisters_def sysargs_rel_n_def invs_valid_objs' invs_no_0_obj' split: if_split)
  apply (rule conjI)
   apply (cases args, simp)
   apply (case_tac list, simp)
   apply (case_tac lista, clarsimp simp: unat_eq_0)
   apply fastforce
  apply (clarsimp simp: frame_gp_registers_convs word_less_nat_alt
                        sysargs_rel_def n_frameRegisters_def n_msgRegisters_def
                  split: if_split_asm)
  apply (simp add: invs_weak_sch_act_wf invs_valid_objs' invs_queues)
  apply (fastforce dest!: global'_no_ex_cap simp: invs'_def valid_state'_def)
  done

lemma invokeTCB_Suspend_ccorres:
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple and tcb_at' t and ex_nonz_cap_to' t)
     (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr t}) []
   (invokeTCB (Suspend t)) (Call invokeTCB_Suspend_'proc)"
  apply (cinit lift: thread_')
   apply (simp add: liftE_def return_returnOk)
   apply (ctac(no_vcg) add: suspend_ccorres[OF cteDeleteOne_ccorres])
    apply (rule ccorres_return_CE, simp+)[1]
   apply wp
  apply clarsimp
  apply (auto simp: invs'_def valid_state'_def global'_no_ex_cap)
  done

lemma invokeTCB_Resume_ccorres:
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and tcb_at' t and ex_nonz_cap_to' t and sch_act_simple)
     (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr t}) []
   (invokeTCB (Resume t)) (Call invokeTCB_Resume_'proc)"
  apply (cinit lift: thread_')
   apply (simp add: liftE_def return_returnOk)
   apply (ctac(no_vcg) add: restart_ccorres)
    apply (rule ccorres_return_CE, simp+)[1]
   apply wp
  apply clarsimp
  done

lemma Arch_decodeTransfer_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call Arch_decodeTransfer_'proc {s'. ret__unsigned_long_' s' = 0}"
  by (vcg, simp)

lemmas ccorres_split_nothrow_dc
    = ccorres_split_nothrow[where r'=dc and xf'=xfdc, OF _ ceqv_refl]

lemmas getRegister_ccorres_defer
    = ccorres_defer[OF getRegister_ccorres, OF no_fail_asUser [OF no_fail_getRegister]]

lemma msg_registers_convs:
  "length X64_H.msgRegisters = unat n_msgRegisters"
  "n < length X64_H.msgRegisters \<Longrightarrow>
     index msgRegistersC n = register_from_H (X64_H.msgRegisters ! n)"
  apply (simp_all add: msgRegisters_unfold
                       X64.msgRegisters_def n_msgRegisters_def
                       msgRegistersC_def fupdate_def Arrays.update_def)
  apply (auto simp: less_Suc_eq fcp_beta)
  done

lemma mapM_x_split_append:
  "mapM_x f xs = do _ \<leftarrow> mapM_x f (take n xs); mapM_x f (drop n xs) od"
  using mapM_x_append[where f=f and xs="take n xs" and ys="drop n xs"]
  by simp

lemma ccorres_abstract_cong:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s ; s' \<in> P'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> a s = b s \<rbrakk> \<Longrightarrow>
   ccorres_underlying sr G r xf ar axf P P' hs a c
        = ccorres_underlying sr G r xf ar axf P P' hs b c"
  by (simp add: ccorres_underlying_def split_paired_Ball imp_conjL
          cong: conj_cong xstate.case_cong)

lemma is_aligned_the_x_strengthen:
  "x \<noteq> None \<and> case_option \<top> valid_ipc_buffer_ptr' x s \<longrightarrow> is_aligned (the x) msg_align_bits"
  by (clarsimp simp: valid_ipc_buffer_ptr'_def)

lemma valid_ipc_buffer_ptr_the_strengthen:
  "x \<noteq> None \<and> case_option \<top> valid_ipc_buffer_ptr' x s \<longrightarrow> valid_ipc_buffer_ptr' (the x) s"
  by clarsimp


lemma lookupIPCBuffer_Some_0:
  "\<lbrace>\<top>\<rbrace> lookupIPCBuffer w t \<lbrace>\<lambda>rv s. rv \<noteq> Some 0\<rbrace>"
  apply (simp add: lookupIPCBuffer_def
                   X64_H.lookupIPCBuffer_def
                   Let_def getThreadBufferSlot_def
                   locateSlot_conv
             cong: if_cong)
  apply (wp haskell_assert_wp | wpc | simp)+
  done

lemma asUser_valid_ipc_buffer_ptr':
  "\<lbrace> valid_ipc_buffer_ptr' p \<rbrace> asUser t m \<lbrace> \<lambda>rv s. valid_ipc_buffer_ptr' p s \<rbrace>"
  by (simp add: valid_ipc_buffer_ptr'_def, wp, auto simp: valid_ipc_buffer_ptr'_def)

lemma invokeTCB_ReadRegisters_ccorres:
notes
  nat_min_simps [simp del]
  wordSize_def' [simp]
  option.case_cong_weak [cong]
  prod.case_cong_weak [cong]
shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart)
              and tcb_at' target and sch_act_simple and (\<lambda>s. target \<noteq> ksIdleThread s)
              and (\<lambda>_. target \<noteq> thread))
       (UNIV
            \<inter> {s. tcb_src_' s = tcb_ptr_to_ctcb_ptr target}
            \<inter> {s. suspendSource_' s = from_bool susp}
            \<inter> {s. n_' s = n}
            \<inter> {s. call_' s = from_bool isCall}) []
       (doE reply \<leftarrow> invokeTCB (ReadRegisters target susp n archCp);
           liftE (replyOnRestart thread reply isCall) odE)
       (Call invokeTCB_ReadRegisters_'proc)"
  supply empty_fail_cond[simp]
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: tcb_src_' suspendSource_' n_' call_'
                simp: invokeTCB_def liftE_bindE bind_assoc)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread,
            rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (rule ccorres_split_nothrow_dc)
        apply (simp add: when_def del: Collect_const split del: if_split)
        apply (rule ccorres_cond2[where R=\<top>], simp add: from_bool_0 Collect_const_mem)
         apply (ctac add: suspend_ccorres[OF cteDeleteOne_ccorres])
        apply (rule ccorres_return_Skip)
       apply (rule ccorres_pre_getCurThread)
       apply (simp only: liftE_bindE[symmetric])
       apply (ctac add: Arch_performTransfer_ccorres)
          apply (simp add: liftE_bindE Collect_False
                      del: Collect_const)
          apply (simp add: replyOnRestart_def liftE_def bind_assoc when_def
                           replyFromKernel_def if_to_top_of_bind setMRs_def
                           zipWithM_x_mapM_x asUser_mapM_x split_def
                      del: Collect_const cong: if_cong)
          apply (rule ccorres_symb_exec_l)
             apply (rule ccorres_symb_exec_l[OF _ _ _ empty_fail_getThreadState])
               apply (rule ccorres_if_lhs[OF _ ccorres_False[where P'=UNIV]])
               apply (rule ccorres_if_lhs)
                apply (simp add: Collect_True whileAnno_def del: Collect_const)
                apply (rule ccorres_rhs_assoc)+
                apply csymbr
                apply (ctac add: lookupIPCBuffer_ccorres)
                  apply (rename_tac state destIPCBuffer ipcBuffer)
                  apply (ctac add: setRegister_ccorres)
                    apply (rule ccorres_stateAssert)
                    apply (rule ccorres_rhs_assoc2)
                    apply (rule_tac P="length reply
                               = min (unat n) (unat n_frameRegisters + unat n_gpRegisters)"
                                in ccorres_gen_asm)
                    apply (rule ccorres_split_nothrow_novcg)
                        apply (rule_tac F="\<lambda>m s. obj_at' (\<lambda>tcb. map ((user_regs o atcbContextGet o tcbArch) tcb) (genericTake n
                                                     (X64_H.frameRegisters @ X64_H.gpRegisters))
                                                              = reply) target s"
                                   in ccorres_mapM_x_while)
                            apply clarsimp
                            apply (rule ccorres_guard_imp2)
                             apply (rule ccorres_add_return,
                                    ctac add: getRegister_ccorres_defer[where thread=target])
                               apply (ctac add: setRegister_ccorres)
                              apply wp
                             apply simp
                             apply (vcg exspec=getRegister_modifies)
                            apply (clarsimp simp: getRegister_def submonad_asUser.guarded_gets)
                            apply (clarsimp simp: simpler_gets_def obj_at'_weakenE[OF _ TrueI]
                                                  msg_registers_convs)
                            apply (cut_tac x=na in unat_of_nat64)
                             apply (simp add: word_bits_def n_msgRegisters_def)
                            apply (simp add: msg_registers_convs n_msgRegisters_def
                                             word_of_nat_less)
                            apply (subgoal_tac "na < unat n_frameRegisters")
                             apply (intro conjI[rotated] allI impI)
                               apply (assumption | erule sym)
                              apply (rule frame_gp_registers_convs)
                              apply (simp add: frame_gp_registers_convs)
                             apply (drule obj_at_ko_at')
                             apply (clarsimp simp: obj_at'_def projectKOs asUser_fetch_def
                                                   frame_gp_registers_convs genericTake_def
                                                   nth_append
                                            split: if_split)
                            apply (simp add: n_frameRegisters_def n_msgRegisters_def)
                           apply (simp add: frame_gp_registers_convs msg_registers_convs
                                            n_msgRegisters_def n_frameRegisters_def
                                            n_gpRegisters_def msgMaxLength_def msgLengthBits_def
                                     split: option.split)
                           apply (simp add: min_def word_less_nat_alt split: if_split)[1]
                           apply arith
                          apply (rule allI, rule conseqPre, vcg exspec=setRegister_modifies
                                                                exspec=getRegister_modifies)
                          apply clarsimp
                         apply (wp asUser_obj_at')
                         apply simp
                        apply (simp add: word_bits_def msgMaxLength_def
                                         msg_registers_convs n_msgRegisters_def)
                       apply ceqv
                      (* got to split reply into frameregisters part and gpregisters
                         part remaining, match against 2nd and 4th loop. 3rd loop
                         never executes with current configuration *)
                      apply (simp add: msg_registers_convs del: Collect_const)
                      apply (rule iffD2 [OF ccorres_abstract_cong])
                       apply (rule bind_apply_cong[OF _ refl])
                       apply (rule_tac n1="min (unat n_frameRegisters - unat n_msgRegisters) (unat n)"
                                   in fun_cong [OF mapM_x_split_append])
                      apply (rule_tac P="destIPCBuffer \<noteq> Some 0" in ccorres_gen_asm)
                      apply (subgoal_tac "(ipcBuffer = NULL) = (destIPCBuffer = None)")
                       prefer 2
                       apply (clarsimp simp: option_to_ptr_def option_to_0_def
                                      split: option.split_asm)
                      apply (simp add: bind_assoc del: Collect_const)
                      apply (rule_tac xf'=i_' and r'="\<lambda>_ rv. unat rv = min (unat n_frameRegisters)
                                                                      (min (unat n)
                                                                           (case destIPCBuffer of None \<Rightarrow> unat n_msgRegisters
                                                                              | _ \<Rightarrow> unat n_frameRegisters))"
                                 in ccorres_split_nothrow_novcg)
                          apply (rule ccorres_Cond_rhs)
                           apply (rule ccorres_rel_imp,
                                  rule_tac F="\<lambda>m s. obj_at' (\<lambda>tcb. map ((user_regs o atcbContextGet o tcbArch) tcb) (genericTake n
                                                      (X64_H.frameRegisters @ X64_H.gpRegisters))
                                                               = reply) target s
                                                 \<and> valid_ipc_buffer_ptr' (the destIPCBuffer) s
                                                 \<and> valid_pspace' s"
                                       and i="unat n_msgRegisters"
                                    in ccorres_mapM_x_while')
                                apply (intro allI impI, elim conjE exE, hypsubst, simp)
                                apply (simp add: less_diff_conv)
                                apply (rule ccorres_guard_imp2)
                                 apply (rule ccorres_add_return,
                                        ctac add: getRegister_ccorres_defer[where thread=target])
                                   apply (rule ccorres_move_array_assertion_ipc_buffer
                                            | (rule ccorres_flip_Guard,
                                                rule ccorres_move_array_assertion_ipc_buffer))+
                                   apply (rule storeWordUser_ccorres)
                                  apply wp
                                 apply (vcg exspec=getRegister_modifies)
                                apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI]
                                                      word_size unat_gt_0 option_to_ptr_def
                                                      option_to_0_def)
                                apply (intro conjI[rotated] impI allI)
                                       apply (simp add: n_msgRegisters_def n_frameRegisters_def
                                                        word_less_nat_alt)
                                       apply (subst unat_add_lem[THEN iffD1], simp_all add: unat_of_nat)[1]
                                      prefer 3
                                      apply (erule sym)
                                     apply (simp add: n_msgRegisters_def msg_registers_convs
                                                      msg_align_bits msgMaxLength_def)
                                     apply (simp(no_asm) add: unat_arith_simps unat_of_nat
                                                        cong: if_cong, simp)
                                    apply (simp add: n_msgRegisters_def msg_registers_convs
                                                     msg_align_bits msgMaxLength_def)
                                    apply (simp(no_asm) add: unat_arith_simps unat_of_nat
                                                       cong: if_cong, simp)
                                   apply (simp add: option_to_ptr_def option_to_0_def
                                                    msg_registers_convs upto_enum_word wordSize_def'
                                              del: upt.simps)
                                  apply (rule frame_gp_registers_convs)
                                  apply (simp add: frame_gp_registers_convs less_diff_conv)
                                  apply (subst iffD1 [OF unat_add_lem])
                                   apply (simp add: n_msgRegisters_def n_frameRegisters_def
                                                    word_le_nat_alt unat_of_nat)
                                  apply (simp add: n_frameRegisters_def n_msgRegisters_def
                                                   unat_of_nat)
                                 apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
                                 apply (erule aligned_add_aligned)
                                  apply (rule is_aligned_mult_triv2[where n=3, simplified])
                                 apply (simp add: msg_align_bits_def word_size_bits_def)
                                apply (clarsimp simp: getRegister_def submonad_asUser.guarded_gets
                                                      obj_at'_weakenE[OF _ TrueI])
                                apply (clarsimp simp: asUser_fetch_def simpler_gets_def
                                                      obj_at'_def projectKOs genericTake_def
                                                      nth_append frame_gp_registers_convs)
                                apply (simp add: n_msgRegisters_def unat_of_nat n_frameRegisters_def)
                                apply (subst iffD1 [OF unat_add_lem])
                                 apply (simp add: unat_of_nat)+
                               apply (clarsimp simp: less_diff_conv)
                               apply (simp add: frame_gp_registers_convs msg_registers_convs
                                                n_msgRegisters_def n_frameRegisters_def
                                                n_gpRegisters_def Types_H.msgMaxLength_def
                                                Types_H.msgLengthBits_def
                                         split: option.split)
                               apply (simp add: min_def word_less_nat_alt split: if_split)[1]
                               apply (simp split: if_split_asm, arith+)[1]
                              apply (rule allI, rule conseqPre, vcg)
                              apply clarsimp
                             apply (wp)
                            apply (clarsimp simp: less_diff_conv)
                            apply (simp add: word_bits_def n_msgRegisters_def n_frameRegisters_def
                                             Types_H.msgLengthBits_def Types_H.msgMaxLength_def
                                             msg_registers_convs)
                           apply (clarsimp simp: n_msgRegisters_def n_frameRegisters_def
                                                 msgMaxLength_def Types_H.msgLengthBits_def
                                                 n_gpRegisters_def msg_registers_convs
                                          split: option.split_asm)
                           apply (simp add: min_def split: if_split_asm if_split)
                          apply (drule_tac s=rv'a in sym, simp)
                          apply (rule_tac P=\<top> and P'="{s. i_' s = rv'a}" in ccorres_inst)
                          apply clarsimp
                          apply (elim disjE impCE)
                            apply (clarsimp simp: word_le_nat_alt linorder_not_less)
                            apply (subst (asm) unat_of_nat64)
                             apply (simp add: n_msgRegisters_def word_bits_def)
                            apply (clarsimp simp: mapM_x_Nil)
                            apply (rule ccorres_guard_imp2, rule ccorres_return_Skip')
                            apply (simp add: n_msgRegisters_def n_frameRegisters_def
                                             n_gpRegisters_def cong: option.case_cong)
                            apply (simp add: min_def split: if_split option.split)
                           apply (simp add: mapM_x_Nil)
                           apply (rule ccorres_guard_imp2, rule ccorres_return_Skip')
                           apply (simp add: n_msgRegisters_def n_frameRegisters_def
                                            n_gpRegisters_def cong: option.case_cong)
                           apply (simp add: min_def split: if_split option.split)
                           apply (clarsimp simp only: unat_arith_simps, simp)
                          apply (clarsimp simp: less_diff_conv word_le_nat_alt linorder_not_less)
                          apply (subst(asm) unat_of_nat64)
                           apply (simp add: word_bits_def n_msgRegisters_def)
                          apply (simp add: mapM_x_Nil n_frameRegisters_def n_gpRegisters_def)
                          apply (rule ccorres_guard_imp2, rule ccorres_return_Skip')
                          apply (simp add: n_msgRegisters_def n_frameRegisters_def
                                           n_gpRegisters_def cong: option.case_cong)
                         apply ceqv
                        apply csymbr
                        apply csymbr
                        apply (rule iffD1[OF ccorres_expand_while_iff_Seq])
                        apply (rule ccorres_cond_false)
                        apply (rule ccorres_split_nothrow_novcg)
                            apply (rule_tac xf'=i_' in ccorres_abstract, ceqv)
                            apply (rename_tac i_c, rule_tac P="i_c = 0" in ccorres_gen_asm2)
                            apply (simp add: drop_zip del: Collect_const)
                            apply (rule ccorres_Cond_rhs)
                             apply (rule_tac F="\<lambda>m s. obj_at' (\<lambda>tcb. map ((user_regs o atcbContextGet o tcbArch) tcb) (genericTake n
                                                       (X64_H.frameRegisters @ X64_H.gpRegisters))
                                                                = reply) target s
                                                  \<and> valid_ipc_buffer_ptr' (the destIPCBuffer) s \<and> valid_pspace' s"
                                        and i="0" in ccorres_mapM_x_while')
                                 apply (clarsimp simp: less_diff_conv drop_zip)
                                 apply (rule ccorres_guard_imp2)
                                  apply (rule ccorres_add_return,
                                         ctac add: getRegister_ccorres_defer[where thread=target])
                                    apply (rule ccorres_move_array_assertion_ipc_buffer
                                             | (rule ccorres_flip_Guard,
                                                 rule ccorres_move_array_assertion_ipc_buffer))+
                                    apply (rule storeWordUser_ccorres)
                                   apply wp
                                  apply (vcg exspec=getRegister_modifies)
                                 apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI]
                                                       word_size unat_gt_0 option_to_ptr_def
                                                       option_to_0_def)
                                 apply (intro conjI[rotated] impI allI)
                                        apply (simp add: n_frameRegisters_def n_msgRegisters_def
                                                         length_msgRegisters word_of_nat_less
                                                         n_gpRegisters_def msgMaxLength_def)
                                       prefer 3
                                       apply (erule sym)
                                      apply (simp add: n_frameRegisters_def n_msgRegisters_def msg_registers_convs
                                                       msg_align_bits msgMaxLength_def)
                                      apply (simp(no_asm) add: unat_arith_simps unat_of_nat
                                                         cong: if_cong, simp)
                                     apply (simp add: n_frameRegisters_def n_msgRegisters_def msg_registers_convs
                                                      msg_align_bits msgMaxLength_def)
                                     apply (simp(no_asm) add: unat_arith_simps unat_of_nat
                                                        cong: if_cong, simp)
                                    apply (simp add: option_to_ptr_def option_to_0_def
                                                     msg_registers_convs upto_enum_word
                                                     n_msgRegisters_def n_frameRegisters_def
                                                     n_gpRegisters_def msgMaxLength_def msgLengthBits_def
                                                del: upt.simps upt_rec_numeral)
                                   apply (rule frame_gp_registers_convs)
                                   apply (simp add: frame_gp_registers_convs n_msgRegisters_def n_frameRegisters_def
                                                    n_gpRegisters_def msgMaxLength_def msgLengthBits_def
                                                    unat_of_nat)
                                  apply (clarsimp simp: valid_ipc_buffer_ptr'_def,
                                         erule aligned_add_aligned)
                                   apply (rule is_aligned_mult_triv2[where n=3, simplified])
                                  apply (simp add: msg_align_bits_def word_size_bits_def)
                                 apply (clarsimp simp: getRegister_def submonad_asUser.guarded_gets
                                                       obj_at'_weakenE[OF _ TrueI])
                                 apply (clarsimp simp: asUser_fetch_def simpler_gets_def
                                                       obj_at'_def projectKOs genericTake_def
                                                       nth_append frame_gp_registers_convs
                                                       n_frameRegisters_def n_gpRegisters_def
                                                       n_msgRegisters_def frame_gp_registers_convs
                                                 cong: if_cong split: if_split)
                                 apply (clarsimp simp: frame_gp_registers_convs n_gpRegisters_def
                                                       min.absorb1 unat_of_nat)
                                apply (clarsimp simp: less_diff_conv)
                                apply (clarsimp simp: nth_append frame_gp_registers_convs
                                                      n_frameRegisters_def n_gpRegisters_def
                                                      n_msgRegisters_def frame_gp_registers_convs
                                                      Types_H.msgMaxLength_def Types_H.msgLengthBits_def
                                                      msg_registers_convs
                                                cong: if_cong split: if_split)
                                apply (simp add: word_less_nat_alt unat_of_nat)
                                apply (simp add: iffD1[OF unat_add_lem] cong: conj_cong)
                                apply (simp add: min_def
                                          split: if_split if_split_asm,
                                       unat_arith,
                                       fastforce simp: unat_eq_0)[1]
                               apply (rule allI, rule conseqPre, vcg)
                               apply clarsimp
                              apply wp
                             apply (simp add: word_bits_def n_frameRegisters_def n_gpRegisters_def
                                              n_msgRegisters_def)
                             apply (simp add: min_less_iff_disj less_imp_diff_less)
                            apply (simp add: drop_zip n_gpRegisters_def)
                            apply (elim disjE impCE)
                             apply (clarsimp simp: mapM_x_Nil cong: ccorres_all_cong)
                             apply (rule ccorres_return_Skip')
                            apply (simp add: linorder_not_less word_le_nat_alt drop_zip
                                             mapM_x_Nil n_frameRegisters_def n_msgRegisters_def
                                       cong: ccorres_all_cong)
                            apply (rule ccorres_guard_imp2, rule ccorres_return_Skip')
                            apply simp
                           apply ceqv
                          apply csymbr
                          apply (rule ccorres_rhs_assoc2)
                          apply (ctac (no_vcg) add: setMessageInfo_ccorres)
                            apply (ctac (no_vcg))
                             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
                             apply (rule allI, rule conseqPre, vcg)
                             apply (clarsimp simp: return_def)
                            apply (wp | simp add: valid_tcb_state'_def)+
                          apply (clarsimp simp: ThreadState_defs mask_def)
                         apply (rule mapM_x_wp')
                         apply (rule hoare_pre)
                          apply (wp sch_act_wf_lift valid_queues_lift tcb_in_cur_domain'_lift)
                         apply clarsimp
                        apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
                        apply (simp add: message_info_to_H_def)
                        apply (clarsimp simp: n_frameRegisters_def n_msgRegisters_def
                                              n_gpRegisters_def field_simps upto_enum_word
                                              word_less_nat_alt Types_H.msgMaxLength_def
                                              Types_H.msgLengthBits_def
                                    simp del: upt.simps
                                       split: option.split_asm)
                         apply (clarsimp simp: min_def iffD2 [OF mask_eq_iff_w2p] word_size
                                               word_less_nat_alt
                                       split: if_split_asm dest!: word_unat.Rep_inverse')
                        apply (clarsimp simp: length_msgRegisters n_msgRegisters_def)
                        apply (clarsimp simp: min_def iffD2 [OF mask_eq_iff_w2p] word_size
                                              word_less_nat_alt
                                      split: if_split_asm dest!: word_unat.Rep_inverse')
                       apply (simp add: pred_conj_def)
                       apply (wp mapM_x_wp' sch_act_wf_lift valid_queues_lift hoare_weak_lift_imp
                                 tcb_in_cur_domain'_lift)
                      apply (simp add: n_frameRegisters_def n_msgRegisters_def
                                       guard_is_UNIV_def)
                     apply simp
                     apply (rule mapM_x_wp')
                     apply (rule hoare_pre)
                      apply (wp asUser_obj_at'[where t'=target] hoare_weak_lift_imp
                                asUser_valid_ipc_buffer_ptr')
                     apply clarsimp
                    apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                                          msg_registers_convs n_msgRegisters_def
                                          n_frameRegisters_def n_gpRegisters_def
                                          msgMaxLength_def msgLengthBits_def
                                          word_less_nat_alt unat_of_nat)
                   apply (wp (once) hoare_drop_imps)
                   apply (wp asUser_obj_at'[where t'=target] hoare_weak_lift_imp
                             asUser_valid_ipc_buffer_ptr')
                  apply (vcg exspec=setRegister_modifies)
                 apply simp
                 apply (strengthen valid_ipc_buffer_ptr_the_strengthen)
                 apply simp
                 apply (wp lookupIPCBuffer_Some_0 | wp (once) hoare_drop_imps)+
                apply (simp add: Collect_const_mem X64_H.badgeRegister_def
                                 X64.badgeRegister_def X64.capRegister_def
                                 "StrictC'_register_defs")
                apply (vcg exspec=lookupIPCBuffer_modifies)
               apply simp
               apply (ctac(no_vcg) add: setThreadState_ccorres)
                apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                apply (rule allI, rule conseqPre, vcg)
                apply (simp add: return_def)
               apply wp+
             apply (simp cong: rev_conj_cong)
             apply wp
             apply (wp asUser_inv mapM_wp' getRegister_inv
                      asUser_get_registers[simplified] hoare_weak_lift_imp)+
            apply (rule hoare_strengthen_post, rule asUser_get_registers)
            apply (clarsimp simp: obj_at'_def genericTake_def
                                  frame_gp_registers_convs)
            apply arith
           apply (wp hoare_weak_lift_imp)
          apply simp
         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
        apply (simp add: performTransfer_def)
        apply wp
       apply (simp add: Collect_const_mem ThreadState_defs mask_def)
       apply vcg
      apply (rule_tac Q="\<lambda>rv. invs' and st_tcb_at' ((=) Restart) thread
                             and tcb_at' target" in hoare_post_imp)
       apply (clarsimp simp: pred_tcb_at')
       apply (auto elim!: pred_tcb'_weakenE)[1]
      apply (wp suspend_st_tcb_at')
     apply (vcg exspec=suspend_modifies)
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (clarsimp simp: rf_sr_ksCurThread ct_in_state'_def
                 split: if_split)
  done

lemma decodeReadRegisters_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and sch_act_simple and (\<lambda>s. ksCurThread s = thread) and ct_active'
              and sysargs_rel args buffer
              and tcb_at' (capTCBPtr cp) and ex_nonz_cap_to' (capTCBPtr cp)
              and K (isThreadCap cp))
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. call_' s = from_bool isCall}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeReadRegisters args cp
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeReadRegisters_'proc)"
  apply (cinit' lift: cap_' length___unsigned_long_' call_' buffer_')
   apply (simp add: decodeReadRegisters_def decodeTransfer_def
               del: Collect_const cong: list.case_cong)
   apply wpc
    apply (drule word_unat.Rep_inverse')
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply wpc
    apply (drule word_unat.Rep_inverse')
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: word_less_nat_alt Collect_False del: Collect_const)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return,
            ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_move_const_guards)+
       apply (simp add: rangeCheck_def unlessE_whenE whenE_def if_to_top_of_bindE
                        ccorres_seq_cond_raise if_to_top_of_bind
                   del: Collect_const)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: frame_gp_registers_convs n_frameRegisters_def
                          n_gpRegisters_def Collect_const_mem)
         apply unat_arith
        apply (simp add: throwError_bind invocationCatch_def
                   cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: throwError_def return_def intr_and_se_rel_def
                              syscall_error_rel_def syscall_error_to_H_cases
                              exception_defs Collect_const_mem)
        apply (simp add: frame_gp_registers_convs n_frameRegisters_def
                         n_gpRegisters_def)
       apply (simp add: ccorres_invocationCatch_Inr returnOk_bind
                        performInvocation_def
                   del: Collect_const)
       apply csymbr
       apply csymbr
       apply csymbr
       apply (simp add: liftE_bindE bind_assoc)
       apply (rule ccorres_pre_getCurThread)
       apply (rule ccorres_cond_seq)
       apply (rule_tac R="\<lambda>s. self = ksCurThread s \<and> isThreadCap cp" and P="\<lambda>s. capTCBPtr cp = self"
                in ccorres_cond_both)
         apply clarsimp
         apply (frule rf_sr_ksCurThread)
         apply clarsimp
         apply (frule (1) cap_get_tag_isCap[symmetric, THEN iffD1])
         apply (drule (1) cap_get_tag_to_H)
         apply clarsimp
         apply (rule iffI)
          apply (drule_tac t="ksCurThread s" in sym)
          apply simp
         apply simp
        apply (rule_tac P="capTCBPtr cp = self" in ccorres_gen_asm)
        apply simp
        apply (simp add: throwError_bind invocationCatch_def
                    cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (rule_tac P="capTCBPtr cp \<noteq> self" in ccorres_gen_asm)
       apply (simp add: returnOk_bind)
       apply (simp add: ccorres_invocationCatch_Inr del: Collect_const)
       apply (ctac add: setThreadState_ccorres)
         apply csymbr
         apply (rule ccorres_Guard_Seq)+
         apply (rule ccorres_nondet_refinement)
          apply (rule is_nondet_refinement_bindE)
           apply (rule is_nondet_refinement_refl)
          apply (simp split: if_split, rule conjI[rotated])
           apply (rule impI, rule is_nondet_refinement_refl)
          apply (rule impI, rule is_nondet_refinement_alternative1)
         apply (simp add: performInvocation_def)
         apply (rule ccorres_add_returnOk)
         apply (ctac(no_vcg) add: invokeTCB_ReadRegisters_ccorres)
           apply (rule ccorres_return_CE, simp+)[1]
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply wp
        apply (wp ct_in_state'_set sts_invs_minor')
       apply (simp add: Collect_const_mem intr_and_se_rel_def
                        cintr_def exception_defs)
       apply (vcg exspec=setThreadState_modifies)
      apply wp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: Collect_const_mem rf_sr_ksCurThread
                        ThreadState_defs word_sless_def word_sle_def
                        mask_eq_iff_w2p word_size isCap_simps
                        ReadRegistersFlags_defs tcb_at_invs'
                        cap_get_tag_isCap capTCBPtr_eq)
  apply (frule global'_no_ex_cap[OF invs_valid_global'], clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (auto simp: ct_in_state'_def n_frameRegisters_def n_gpRegisters_def
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE
              dest!: st_tcb_at_idle_thread')[1]
  apply (clarsimp simp: word_and_1 split: if_split)
  done

lemma decodeWriteRegisters_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and sch_act_simple
              and (\<lambda>s. ksCurThread s = thread) and ct_active' and K (isThreadCap cp)
              and valid_cap' cp and (\<lambda>s. \<forall>x \<in> zobj_refs' cp. ex_nonz_cap_to' x s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeWriteRegisters args cp
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeWriteRegisters_'proc)"
  supply unsigned_numeral[simp del]
  apply (cinit' lift: cap_' length___unsigned_long_' buffer_' simp: decodeWriteRegisters_def)
   apply (rename_tac length' cap')
   apply (rule ccorres_Cond_rhs_Seq)
    apply wpc
     apply (simp add: throwError_bind invocationCatch_def
                cong: StateSpace.state.fold_congs globals.fold_congs)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: word_less_nat_alt)
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: word_less_nat_alt del: Collect_const)
   apply (rule_tac P="\<lambda>a. ccorres rvr xf P P' hs a c" for rvr xf P P' hs c in ssubst,
          rule bind_cong [OF _ refl], rule list_case_helper,
          clarsimp)+
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule_tac P="unat (of_nat (length args) :: machine_word) = length args"
                    in ccorres_gen_asm)
       apply (simp add: unat_sub word_le_nat_alt genericLength_def
                        word_less_nat_alt hd_drop_conv_nth2
                   del: Collect_const)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: whenE_def throwError_bind invocationCatch_def
                   cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: whenE_def decodeTransfer_def returnOk_bind del: Collect_const)
       apply csymbr
       apply csymbr
       apply csymbr
       apply (simp add: liftE_bindE bind_assoc)
       apply (rule ccorres_pre_getCurThread)
       apply (rule ccorres_cond_seq)
       apply (rule_tac R="\<lambda>s. self = ksCurThread s \<and> isThreadCap cp" and P="\<lambda>s. capTCBPtr cp = self"
                in ccorres_cond_both)
         apply clarsimp
         apply (frule rf_sr_ksCurThread)
         apply clarsimp
         apply (frule (1) cap_get_tag_isCap[symmetric, THEN iffD1])
         apply (drule (1) cap_get_tag_to_H)
         apply clarsimp
         apply (rule iffI)
          apply (drule_tac t="ksCurThread s" in sym)
          apply simp
         apply simp
        apply (rule_tac P="capTCBPtr cp = self" in ccorres_gen_asm)
        apply simp
        apply (simp add: throwError_bind invocationCatch_def
                    cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (rule_tac P="capTCBPtr cp \<noteq> self" in ccorres_gen_asm)
       apply (simp add: returnOk_bind)
       apply (simp add: ccorres_invocationCatch_Inr del: Collect_const)
       apply (ctac add: setThreadState_ccorres)
         apply (rule ccorres_Guard_Seq)+
         apply (simp add: performInvocation_def)
         apply (ctac(no_vcg) add: invokeTCB_WriteRegisters_ccorres
                                    [where args=args and someNum="unat (args ! 1)"])
           apply simp
           apply (rule ccorres_alternative2, rule ccorres_return_CE, simp+)
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply wp[1]
        apply simp
        apply (wp sts_invs_minor' setThreadState_sysargs_rel)
       apply (simp add: Collect_const_mem cintr_def intr_and_se_rel_def
                        exception_defs)
       apply (vcg exspec=setThreadState_modifies)
      apply wp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: Collect_const_mem ct_in_state'_def pred_tcb_at')
  apply (simp add: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: valid_cap'_def ThreadState_defs
                        mask_eq_iff_w2p word_size rf_sr_ksCurThread
                        WriteRegisters_resume_def word_sle_def word_sless_def
                        numeral_eqs)
  apply (frule arg_cong[where f="\<lambda>x. unat (of_nat x :: machine_word)"],
         simp(no_asm_use) only: word_unat.Rep_inverse,
         simp)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def word_less_nat_alt)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def word_less_nat_alt)
   apply (auto simp: genericTake_def cur_tcb'_def linorder_not_less word_le_nat_alt
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  apply (intro allI impI)
  apply (rule disjCI2)
  apply (clarsimp simp: genericTake_def linorder_not_less)
  apply (subst hd_conv_nth, clarsimp simp: unat_eq_0)
  apply (clarsimp simp: word_and_1 split: if_split)
  done

lemma excaps_map_Nil: "(excaps_map caps = []) = (caps = [])"
  by (simp add: excaps_map_def)

lemma decodeCopyRegisters_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and sch_act_simple
              and (\<lambda>s. ksCurThread s = thread) and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and tcb_at' (capTCBPtr cp) and ex_nonz_cap_to' (capTCBPtr cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and sysargs_rel args buffer
              and K (isThreadCap cp))
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeCopyRegisters args cp (map fst extraCaps)
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeCopyRegisters_'proc)"
  apply (cinit' lift: cap_' length___unsigned_long_' current_extra_caps_' buffer_' simp: decodeCopyRegisters_def)
   apply csymbr
   apply wpc
    apply (simp add: if_1_0_0 unat_eq_0)
    apply (rule ccorres_cond_true_seq)
    apply (simp add: invocationCatch_def throwError_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp del: Collect_const)
   apply (subst unat_eq_0[symmetric], simp add: Collect_False del: Collect_const)
   apply csymbr
   apply (simp add: interpret_excaps_test_null decodeTransfer_def
               del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: excaps_map_def invocationCatch_def throwError_bind null_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: excaps_map_def null_def del: Collect_const)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_symb_exec_r)
       apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
       apply (rule ccorres_move_c_guard_cte)
       apply ctac
         apply csymbr
         apply (simp add: cap_get_tag_isCap del: Collect_const)
         apply (rule ccorres_assert2)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (rule_tac P="Q' (capTCBPtr rva) rva" for Q'
                     in ccorres_inst)
          apply (rule ccorres_rhs_assoc)+
          apply (csymbr, csymbr)
          apply (simp add: hd_map del: Collect_const,
                 simp add: hd_conv_nth del: Collect_const)
          apply (simp only: cap_get_tag_isCap[symmetric],
                 drule(1) cap_get_tag_to_H)
          apply (simp add: case_bool_If if_to_top_of_bindE
                           if_to_top_of_bind
                      del: Collect_const cong: if_cong)
          apply (simp add: returnOk_bind Collect_True
                           ccorres_invocationCatch_Inr performInvocation_def
                      del: Collect_const)
          apply (ctac add: setThreadState_ccorres)
            apply csymbr
            apply (rule ccorres_Guard_Seq)+
            apply (ctac add: invokeTCB_CopyRegisters_ccorres)
               apply simp
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE, simp+)[1]
              apply (rule ccorres_return_C_errorE, simp+)[1]
             apply wp
            apply (simp add: cintr_def intr_and_se_rel_def exception_defs)
            apply (vcg exspec=invokeTCB_CopyRegisters_modifies)
           apply (wp sts_invs_minor')
          apply (simp add: Collect_const_mem)
          apply (vcg exspec=setThreadState_modifies)
         apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
          apply vcg
         apply (rule conseqPre, vcg)
         apply (simp add: hd_map isCap_simps hd_conv_nth)
         apply (clarsimp simp: invocationCatch_def throwError_bind
                        split: capability.split,
                auto simp: throwError_def return_def intr_and_se_rel_def
                           syscall_error_rel_def syscall_error_to_H_cases
                           exception_defs)[1]
        apply (simp add: getSlotCap_def)
        apply (wp getCTE_wp)
       apply (simp add: Collect_const_mem if_1_0_0 cap_get_tag_isCap)
       apply vcg
      apply (simp add: Collect_const_mem)
      apply vcg
     apply (rule conseqPre, vcg)
     apply clarsimp
    apply wp
   apply (simp add: Collect_const_mem)
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: Collect_const_mem excaps_map_Nil)
  apply (rule conjI)
   apply (clarsimp simp: excaps_in_mem_def neq_Nil_conv
                         slotcap_in_mem_def cte_wp_at_ctes_of
                         ct_in_state'_def pred_tcb_at')
   apply (rule conjI)
    apply (clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (clarsimp simp: isCap_simps simp del: capMasterCap_maskCapRights)
   apply (frule ctes_of_valid', clarsimp+)
   apply (auto simp: valid_cap'_def excaps_map_def valid_tcb_state'_def
              elim!: pred_tcb'_weakenE
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: word_sle_def CopyRegistersFlags_defs word_sless_def
                        ThreadState_defs rf_sr_ksCurThread
                 split: if_split)
  apply (drule interpret_excaps_eq)
  apply (clarsimp simp: mask_def excaps_map_def split_def ccap_rights_relation_def
                        rightsFromWord_wordFromRights excaps_map_Nil)
  apply (simp only: cap_get_tag_isCap[symmetric],
         drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: cap_get_tag_isCap to_bool_def)
  apply (auto simp: unat_eq_of_nat word_and_1_shiftls
    word_and_1_shiftl [where n=3,simplified] cap_get_tag_isCap[symmetric] split: if_split_asm)
  done

method wrong_cap_throwError_ccorres = solves \<open>
        (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
      , vcg
      , (rule conseqPre, vcg)
      , (auto simp: syscall_error_rel_def syscall_error_to_H_cases isCap_simps
                            exception_defs throwError_def return_def if_1_0_0
                     split: capability.split arch_capability.split if_split_asm)[1]
   \<close>

add_try_method wrong_cap_throwError_ccorres

lemma checkValidIPCBuffer_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs') (UNIV \<inter> {s. vptr_' s = vptr} \<inter> {s. ccap_relation cp (cap_' s)}) []
       (checkValidIPCBuffer vptr cp)
       (Call checkValidIPCBuffer_'proc)"
  apply (simp add:checkValidIPCBuffer_def X64_H.checkValidIPCBuffer_def)
  apply (cases "isArchPageCap cp \<and> \<not> isDeviceCap cp")
   apply (simp only: isCap_simps isDeviceCap.simps, safe)[1]
   apply (cinit lift: vptr_' cap_')
    apply (simp add: X64_H.checkValidIPCBuffer_def  if_1_0_0 del: Collect_const)
    apply csymbr
    apply (rule ccorres_cond_false_seq)
    apply simp
    apply csymbr
    apply (rule ccorres_cond_false_seq)
    apply clarsimp
    apply (simp only:Cond_if_mem)
    apply (rule ccorres_Cond_rhs_Seq)
     apply (clarsimp simp add: msgAlignBits_def mask_def whenE_def)
     apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
      apply vcg
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def exception_defs
                           syscall_error_rel_def syscall_error_to_H_cases)
    apply (simp add: whenE_def msgAlignBits_def mask_def)
    apply (rule ccorres_return_CE, simp+)[1]
   apply (clarsimp simp: cap_get_tag_isCap isCap_simps pageSize_def
                         Collect_const_mem if_1_0_0 ccap_relation_page_is_device
                         word_sle_def)
  apply (cases "isArchPageCap cp")
   apply (simp only: isCap_simps isDeviceCap.simps)[1]
   apply clarsimp
   apply (cinit lift: vptr_' cap_')
    apply (simp add: X64_H.checkValidIPCBuffer_def  if_1_0_0 del: Collect_const)
    apply csymbr
    apply (rule ccorres_cond_false_seq)
    apply simp
    apply csymbr
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def exception_defs
                          syscall_error_rel_def syscall_error_to_H_cases)
   apply (simp add: cap_get_tag_isCap isCap_simps pageSize_def ccap_relation_page_is_device)
  apply (cinit' lift: vptr_' cap_')
   apply csymbr
   apply (simp add: X64_H.checkValidIPCBuffer_def cap_get_tag_isCap)
   apply (wpc; wrong_cap_throwError_ccorres)
  apply clarsimp
  done

lemma slotCapLongRunningDelete_ccorres:
  "ccorres ((=) \<circ> from_bool) ret__unsigned_long_' invs'
           (UNIV \<inter> {s. slot_' s = cte_Ptr slot}) []
     (slotCapLongRunningDelete slot) (Call slotCapLongRunningDelete_'proc)"
  supply subst_all [simp del]
  apply (cinit lift: slot_')
   apply (simp add: case_Null_If del: Collect_const)
   apply (rule ccorres_pre_getCTE)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule_tac P="cte_wp_at' ((=) cte) slot"
                in ccorres_cross_over_guard)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_if_lhs)
      apply (rule ccorres_cond_true_seq)
      apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
      apply vcg
     apply (rule ccorres_cond_false_seq)
     apply (rule ccorres_rhs_assoc)+
     apply (rule_tac xf'=ret__unsigned_long_' in ccorres_split_nothrow_novcg)
         apply (ctac add: isFinalCapability_ccorres[where slot=slot])
        apply (rule Seq_weak_ceqv)
        apply (rule Cond_ceqv [OF _ ceqv_refl ceqv_refl])
        apply simp
        apply (rule impI, rule sym, rule mem_simps)
       apply (clarsimp simp del: Collect_const)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
        apply vcg
       apply (simp del: Collect_const)
       apply (rule ccorres_move_c_guard_cte)
       apply (rule_tac P="cte_wp_at' ((=) cte) slot"
                  in  ccorres_from_vcg_throws[where P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: cte_wp_at_ctes_of return_def)
       apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
       apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap
                             from_bool_0
                      dest!: ccte_relation_ccap_relation)
       apply (simp add: from_bool_def
                 split: bool.split)
       apply (auto simp add: longRunningDelete_def isCap_simps
                 split: capability.split)[1]
      apply simp
      apply (wp hoare_drop_imps isFinalCapability_inv)
     apply (clarsimp simp: Collect_const_mem guard_is_UNIV_def)
     apply (rename_tac rv')
     apply (case_tac rv'; clarsimp simp: false_def)
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap map_comp_Some_iff
                 dest!: ccte_relation_ccap_relation)
  done

definition
  isValidVTableRoot_C :: "cap_C \<Rightarrow> bool"
where
 "isValidVTableRoot_C cap \<equiv> cap_get_tag cap = scast cap_pml4_cap
             \<and> to_bool (capPML4IsMapped_CL (cap_pml4_cap_lift cap))"

lemma isValidVTableRoot_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call isValidVTableRoot_'proc
    {s'. ret__unsigned_long_' s' = from_bool (isValidVTableRoot_C (cap_' s))}"
  apply vcg
  apply (clarsimp simp: isValidVTableRoot_C_def if_1_0_0 from_bool_0)
  apply (simp add: to_bool_def split: if_split)
  done

lemma isValidVTableRoot_conv:
  "\<lbrakk> ccap_relation cap cap' \<rbrakk>
      \<Longrightarrow> isValidVTableRoot_C cap' = isValidVTableRoot cap"
  apply (clarsimp simp: isValidVTableRoot_C_def
                        if_1_0_0 from_bool_0 isValidVTableRoot_def
                        X64_H.isValidVTableRoot_def)
  apply (case_tac "isArchCap_tag (cap_get_tag cap')")
   apply (clarsimp simp: cap_get_tag_isCap cap_get_tag_isCap_ArchObject)
   apply (case_tac "cap_get_tag cap' = scast cap_pml4_cap")
    apply (clarsimp split: arch_capability.split simp: isCap_simps)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2
                          cap_pml4_cap_lift cap_to_H_def)
    apply (clarsimp split: if_split)
   apply (clarsimp simp: cap_get_tag_isCap cap_get_tag_isCap_ArchObject)
   apply (simp split: arch_capability.split_asm add: isCap_simps)
  apply (case_tac "cap_get_tag cap' = scast cap_pml4_cap")
   apply (clarsimp simp: cap_pml4_cap_def isArchCap_tag_def2)
  apply (clarsimp simp: cap_get_tag_isCap split: capability.split_asm)
  done

lemma updateCapData_spec:
  "\<forall>cap preserve newData. \<Gamma>\<turnstile> \<lbrace>ccap_relation cap \<acute>cap \<and> preserve = to_bool \<acute>preserve \<and> newData = \<acute>newData\<rbrace>
             Call updateCapData_'proc
         \<lbrace>ccap_relation (RetypeDecls_H.updateCapData preserve newData cap) \<acute>ret__struct_cap_C\<rbrace>"
  by (simp add: updateCapData_spec)

lemma length_excaps_map:
  "length (excaps_map xcs) = length xcs"
  by (simp add: excaps_map_def)

lemma getSyscallArg_ccorres_foo':
  "ccorres (\<lambda>a rv. rv = ucast (args ! n)) (\<lambda>x. ucast (ret__unsigned_long_' x))
         (sysargs_rel args buffer and sysargs_rel_n args buffer n)
         (UNIV \<inter> \<lbrace>unat \<acute>i = n\<rbrace> \<inter> \<lbrace>\<acute>ipc_buffer = option_to_ptr buffer\<rbrace>) []
    (return ()) (Call getSyscallArg_'proc)"
  apply (insert getSyscallArg_ccorres_foo
          [where args=args and n=n and buffer=buffer])
  apply (clarsimp simp: ccorres_underlying_def)
  apply  (erule (1) my_BallE)
  apply clarsimp
  apply (erule allE, erule allE, erule (1) impE)
  apply (clarsimp simp: return_def unif_rrel_def split: xstate.splits)
  done

lemma scast_mask_8:
  "scast (mask 8 :: sword32) = (mask 8 :: word32)"
  by (clarsimp simp: mask_def)

lemma tcb_at_capTCBPtr_CL:
  "ccap_relation cp cap \<Longrightarrow> valid_cap' cp s
    \<Longrightarrow> isThreadCap cp
    \<Longrightarrow> tcb_at' (cap_thread_cap_CL.capTCBPtr_CL
        (cap_thread_cap_lift cap) && ~~mask tcbBlockSizeBits) s"
  apply (clarsimp simp: cap_get_tag_isCap[symmetric]
                        valid_cap_simps'
                 dest!: cap_get_tag_to_H)
  apply (frule ctcb_ptr_to_tcb_ptr_mask[OF tcb_aligned'], simp)
  done

lemma checkPrio_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (tcb_at' auth)
      (UNIV \<inter> {s. prio_' s = prio} \<inter> {s. auth_' s = tcb_ptr_to_ctcb_ptr auth}) []
      (checkPrio prio auth)
      (Call checkPrio_'proc)"
  apply (cinit lift: prio_' auth_')
   apply (clarsimp simp: liftE_bindE)
   apply (rule ccorres_split_nothrow_novcg[where r'="\<lambda>rv rv'. rv' = ucast rv" and xf'=mcp_'])
       apply (rule threadGet_vcg_corres)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: rf_sr_ksCurThread obj_at'_def projectKOs
                             typ_heap_simps' ctcb_relation_def)
      apply ceqv
     apply (simp add: whenE_def del: Collect_const split: if_split)
     apply (rule conjI; clarsimp)
      apply (rule ccorres_from_vcg_split_throws)
       apply vcg
      apply (rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def syscall_error_rel_def syscall_error_to_H_cases
                            exception_defs Collect_const_mem rf_sr_ksCurThread return_def
                            seL4_MinPrio_def minPriority_def)
     apply clarsimp
     apply (rule ccorres_return_CE)
       apply clarsimp+
    apply wp
   apply (simp add: guard_is_UNIV_def)+
  done

lemma mcpriority_tcb_at'_prio_bounded':
  assumes "mcpriority_tcb_at' (\<lambda>mcp. prio \<le> ucast mcp) t s"
          "priorityBits \<le> len_of TYPE('a)"
  shows "(prio::'a::len word) \<le> ucast (max_word :: priority)"
  using assms
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def priorityBits_def ucast_le_ucast
               simp del: unsigned_uminus1
               elim!: order.trans)

lemmas mcpriority_tcb_at'_prio_bounded
  = mcpriority_tcb_at'_prio_bounded'[simplified priorityBits_def]

lemma decodeTCBConfigure_ccorres:
  notes tl_drop_1[simp] scast_mask_8 [simp]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and sch_act_simple
              and (\<lambda>s. ksCurThread s = thread) and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and valid_cap' cp and cte_at' slot and K (isThreadCap cp)
              and ex_nonz_cap_to' (capTCBPtr cp) and tcb_at' (capTCBPtr cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. slot_' s = cte_Ptr slot}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeTCBConfigure args cp slot extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeTCBConfigure_'proc)"
  apply (cinit' lift: cap_' length___unsigned_long_' slot_' current_extra_caps_' buffer_'
                simp: decodeTCBConfigure_def)
   apply csymbr
   apply (clarsimp cong: StateSpace.state.fold_congs globals.fold_congs
               simp del: Collect_const
               simp add: interpret_excaps_test_null2 excaps_map_Nil)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_cond_true_seq | simp)+
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: if_1_0_0 word_less_nat_alt)
    apply (clarsimp split: list.split
                     simp: throwError_def invocationCatch_def fst_return
                           intr_and_se_rel_def
                           Collect_const_mem syscall_error_rel_def
                           exception_defs syscall_error_to_H_cases)
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_cond_true_seq | simp)+
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: if_1_0_0 word_less_nat_alt)
    apply (clarsimp split: list.split
                     simp: throwError_def invocationCatch_def fst_return
                           intr_and_se_rel_def
                           Collect_const_mem syscall_error_rel_def
                           exception_defs syscall_error_to_H_cases)
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_cond_true_seq | simp)+
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: if_1_0_0 word_less_nat_alt)
    apply (clarsimp split: list.split
                     simp: throwError_def invocationCatch_def fst_return
                           intr_and_se_rel_def excaps_map_def
                           Collect_const_mem syscall_error_rel_def
                           exception_defs syscall_error_to_H_cases)
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_cond_true_seq | simp)+
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: if_1_0_0 word_less_nat_alt)
    apply (clarsimp split: list.split
                     simp: throwError_def invocationCatch_def fst_return
                           intr_and_se_rel_def excaps_map_def
                           Collect_const_mem syscall_error_rel_def
                           exception_defs syscall_error_to_H_cases)
   apply (simp add: if_1_0_0 word_less_nat_alt linorder_not_less
               del: Collect_const)
   apply (rename_tac length' cap')
   apply (subgoal_tac "length extraCaps \<ge> 3")
    prefer 2
    apply (clarsimp simp: idButNot_def interpret_excaps_test_null
                          excaps_map_def neq_Nil_conv)
   apply (thin_tac "P \<longrightarrow> index exc n \<noteq> NULL" for P exc n)+
   apply (rule_tac P="\<lambda>a. ccorres rvr xf P P' hs a c" for rvr xf P P' hs c in ssubst,
          rule bind_cong [OF _ refl], rule list_case_helper, clarsimp)+
   apply (simp add: hd_drop_conv_nth2 del: Collect_const)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return,
            ctac add: getSyscallArg_ccorres_foo'[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_add_return,
              ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
         apply (rule ccorres_add_return,
                ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
           apply csymbr
           apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
           apply (rule ccorres_move_c_guard_cte)
           apply ctac
             apply (rule ccorres_assert2)
             apply csymbr
             apply (rule ccorres_move_c_guard_cte)
             apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=1])
             apply ctac
               apply (rule ccorres_assert2)
               apply csymbr
               apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=2])
               apply (rule ccorres_move_c_guard_cte)
               apply ctac
                 apply (rule ccorres_assert2)
                 apply (simp add: decodeSetIPCBuffer_def split_def
                                  bindE_assoc invocationCatch_use_injection_handler
                                  injection_bindE[OF refl refl] injection_handler_returnOk
                                  injection_handler_If
                             del: Collect_const cong: if_cong)
                 apply (rule_tac xf'="\<lambda>s. (bufferCap_' s, bufferSlot_' s)" and
                                 r'="\<lambda>v (cp', sl'). case v of None \<Rightarrow> args ! 3 = 0 \<and> sl' = cte_Ptr 0
                                                            | Some (cp, sl) \<Rightarrow> ccap_relation cp cp'
                                                                               \<and> args ! 3 \<noteq> 0
                                                                               \<and> sl' = cte_Ptr sl"
                                 in ccorres_splitE)
                     apply (rule ccorres_cond2[where R=\<top>])
                       apply (clarsimp simp add: Collect_const_mem numeral_eqs)
                      apply (rule_tac P="\<lambda>s. args ! 3 = 0" in ccorres_from_vcg[where P'=UNIV])
                      apply (rule allI, rule conseqPre, vcg)
                      apply (clarsimp simp: returnOk_def return_def)
                     apply (rule ccorres_rhs_assoc)+
                     apply (rule ccorres_split_nothrowE)
                          apply (simp add: numeral_eqs)
                          apply (ctac add: ccorres_injection_handler_csum1[OF deriveCap_ccorres])
                         apply ceqv
                        apply simp
                        apply (clarsimp simp: numeral_eqs)
                        apply csymbr
                        apply (rule ccorres_split_nothrowE)
                             apply (ctac add: ccorres_injection_handler_csum1[OF checkValidIPCBuffer_ccorres])
                            apply ceqv
                           apply (match premises in "ccap_relation _ (deriveCap_ret_C.cap_C ccap)" for ccap
                                    \<Rightarrow> \<open>rule ccorres_from_vcg
                                          [where P'="{s. bufferCap_' s = (deriveCap_ret_C.cap_C ccap)
                                                         \<and> bufferSlot_' s = cte_Ptr (snd (extraCaps ! 2))}"
                                             and P="\<lambda>s. args ! 3 \<noteq> 0"]\<close>)
                           apply (rule allI, rule conseqPre, vcg)
                           apply (clarsimp simp: returnOk_def return_def numeral_eqs)
                          apply (rule_tac P'="{s. err' = errstate s}"
                                          in ccorres_from_vcg_throws[where P=\<top>])
                          apply (rule allI, rule conseqPre, vcg)
                          apply (clarsimp simp: throwError_def return_def
                                                syscall_error_rel_def
                                                intr_and_se_rel_def)
                         apply wp
                        apply simp
                        apply (vcg exspec=checkValidIPCBuffer_modifies)
                       apply simp
                       apply (rule_tac P'="{s. err' = errstate s}"
                                       in  ccorres_from_vcg_split_throws[where P=\<top>])
                        apply vcg
                       apply (rule conseqPre, vcg)
                       apply (clarsimp simp: throwError_def return_def
                                             intr_and_se_rel_def syscall_error_rel_def)
                      apply simp
                      apply (wp injection_wp_E [OF refl])
                     apply (simp add: all_ex_eq_helper Collect_const_mem numeral_eqs)
                     apply (vcg exspec=deriveCap_modifies)
                    apply (rule ceqv_tuple2, ceqv, ceqv)
                   apply (rename_tac rv'dc)
                   apply (rule_tac P="P (fst rv'dc) (snd rv'dc)"
                               and P'="P' (fst rv'dc) (snd rv'dc)"
                               for P P' in ccorres_inst)
                   apply (clarsimp simp: tcb_cnode_index_defs
                                           [THEN ptr_add_assertion_positive
                                             [OF ptr_add_assertion_positive_helper]]
                                   simp del: Collect_const)
                   apply csymbr
                   apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq)+
                   apply (simp add: decodeSetSpace_def injection_bindE[OF refl] split_def
                               del: Collect_const)
                   apply (simp add: injection_liftE[OF refl] bindE_assoc
                                    liftM_def getThreadCSpaceRoot
                                    getThreadVSpaceRoot del: Collect_const)
                   apply (simp add: liftE_bindE del: Collect_const)
                   apply (rule ccorres_rhs_assoc)+
                   apply (ctac add: slotCapLongRunningDelete_ccorres)
                     apply (rule ccorres_move_array_assertion_tcb_ctes)
                     apply (simp del: Collect_const)
                     apply csymbr
                     apply (clarsimp simp add: if_1_0_0 from_bool_0
                                     simp del: Collect_const)
                     apply (rule ccorres_Cond_rhs_Seq)
                      apply (rule ccorres_symb_exec_l3
                                    [OF _ _ _ empty_fail_slotCapLongRunningDelete])
                        apply (simp add: unlessE_def injection_handler_throwError
                                    cong: StateSpace.state.fold_congs globals.fold_congs)
                        apply (rule ccorres_cond_true_seq)
                        apply (rule syscall_error_throwError_ccorres_n)
                        apply (simp add: syscall_error_to_H_cases)
                       apply wp+
                     apply (rule ccorres_rhs_assoc)+
                     apply csymbr
                     apply (simp del: Collect_const)
                     apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq
                                 ccorres_rhs_assoc)+
                     apply (ctac add: slotCapLongRunningDelete_ccorres)
                       apply (rule ccorres_move_array_assertion_tcb_ctes)
                       apply (simp del: Collect_const)
                       apply csymbr
                       apply (clarsimp simp add: if_1_0_0 from_bool_0
                                       simp del: Collect_const)
                       apply (rule ccorres_Cond_rhs_Seq)
                        apply (simp add: unlessE_def injection_handler_throwError
                                    cong: StateSpace.state.fold_congs globals.fold_congs)
                        apply (rule syscall_error_throwError_ccorres_n)
                        apply (simp add: syscall_error_to_H_cases)
                       apply (simp add: unlessE_def injection_handler_returnOk
                                   del: Collect_const)
                       apply (rule ccorres_add_return,
                              rule_tac r'="\<lambda>rv rv'. ccap_relation
                                                      (if args ! 1 = 0
                                                       then fst (hd extraCaps)
                                                       else updateCapData False (args ! 1) (fst (hd extraCaps))) rv'"
                                   and xf'="cRootCap_'"
                                   in ccorres_split_nothrow)
                           apply (rule_tac P'="{s. cRootCap = cRootCap_' s}"
                                          in ccorres_from_vcg[where P=\<top>])
                           apply (rule allI, rule conseqPre, vcg)
                           apply (subgoal_tac "extraCaps \<noteq> []")
                            apply (clarsimp simp: returnOk_def return_def hd_conv_nth)
                            apply fastforce
                           apply clarsimp
                          apply ceqv
                         apply (ctac add: ccorres_injection_handler_csum1
                                            [OF deriveCap_ccorres])
                            apply (simp add: Collect_False del: Collect_const)
                            apply (csymbr, csymbr)
                            apply (simp add: cap_get_tag_isCap cnode_cap_case_if
                                        del: Collect_const)
                            apply (rule ccorres_Cond_rhs_Seq)
                             apply (simp add: injection_handler_throwError
                                         cong: StateSpace.state.fold_congs globals.fold_congs)
                             apply (rule syscall_error_throwError_ccorres_n)
                             apply (simp add: syscall_error_to_H_cases)
                            apply (simp add: injection_handler_returnOk del: Collect_const)
                            apply (rule ccorres_add_return,
                                   rule_tac r'="\<lambda>rv rv'. ccap_relation
                                                           (if args ! 2 = 0
                                                            then fst (extraCaps ! Suc 0)
                                                            else updateCapData False (args ! 2) (fst (extraCaps ! Suc 0))) rv'"
                                        and xf'="vRootCap_'"
                                        in ccorres_split_nothrow)
                                apply (rule_tac P'="{s. vRootCap = vRootCap_' s}"
                                                in ccorres_from_vcg[where P=\<top>])
                                apply (rule allI, rule conseqPre, vcg)
                                apply (clarsimp simp: returnOk_def return_def
                                                      hd_drop_conv_nth2)
                                apply fastforce
                               apply ceqv
                              apply (ctac add: ccorres_injection_handler_csum1
                                                 [OF deriveCap_ccorres])
                                 apply (simp add: Collect_False del: Collect_const)
                                 apply csymbr
                                 apply csymbr
                                 apply (simp add: from_bool_0 isValidVTableRoot_conv del: Collect_const)
                                 apply (rule ccorres_Cond_rhs_Seq)
                                  apply (simp add: injection_handler_throwError
                                              cong: StateSpace.state.fold_congs globals.fold_congs)
                                  apply (rule syscall_error_throwError_ccorres_n)
                                  apply (simp add: syscall_error_to_H_cases)
                                 apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                                  performInvocation_def)
                                 apply (ctac add: setThreadState_ccorres)
                                   apply csymbr
                                   apply (ctac(no_vcg) add: invokeTCB_ThreadControl_ccorres)
                                     apply (simp, rule ccorres_alternative2)
                                     apply (rule ccorres_return_CE, simp+)
                                    apply (rule ccorres_return_C_errorE, simp+)[1]
                                   apply wp
                                  apply (simp add: o_def)
                                  apply (wp sts_invs_minor' hoare_case_option_wp)
                                 apply (simp add: Collect_const_mem cintr_def intr_and_se_rel_def
                                                  exception_defs
                                            cong: option.case_cong)
                                 apply (vcg exspec=setThreadState_modifies)
                                apply simp
                                apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
                                apply vcg
                               apply simp
                               apply (wp injection_wp_E[OF refl] hoare_drop_imps)
                              apply (vcg exspec=deriveCap_modifies)
                             apply (simp add: pred_conj_def cong: if_cong)
                             apply wp
                            apply (simp add: Collect_const_mem)
                            apply (vcg)
                           apply simp
                           apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
                           apply vcg
                          apply (simp cong: if_cong)
                          apply (wp injection_wp_E[OF refl] hoare_drop_imps)
                         apply (simp add: Collect_const_mem intr_and_se_rel_def
                                          syscall_error_rel_def exception_defs
                                    cong: option.case_cong sum.case_cong)
                         apply (simp add: all_ex_eq_helper numeral_eqs)
                         apply (vcg exspec=deriveCap_modifies)
                        apply (simp cong: if_cong)
                        apply wp
                       apply (simp add: Collect_const_mem del: Collect_const)
                       apply vcg
                      apply (simp cong: if_cong)
                      apply (wp | wp (once) hoare_drop_imps)+
                     apply (simp add: Collect_const_mem all_ex_eq_helper
                                cong: option.case_cong)
                     apply (vcg exspec=slotCapLongRunningDelete_modifies)
                    apply (simp cong: if_cong)
                    apply (wp | wp (once) hoare_drop_imps)+
                   apply (simp add: Collect_const_mem)
                   apply (vcg exspec=slotCapLongRunningDelete_modifies)
                  apply (simp add: pred_conj_def cong: if_cong)
                  apply (wp injection_wp_E[OF refl] checkValidIPCBuffer_ArchObject_wp)
                  apply simp
                  apply (wp | wp (once) hoare_drop_imps)+
                 apply (simp add: Collect_const_mem all_ex_eq_helper)
                 apply (rule_tac P="{s. cRootCap_' s = cRootCap \<and> vRootCap_' s = vRootCap
                                        \<and> bufferAddr_' s = args ! 3
                                        \<and> ccap_relation cp cap' \<and> isThreadCap cp
                                        \<and> is_aligned (capTCBPtr cp) tcbBlockSizeBits
                                        \<and> ksCurThread_' (globals s) = tcb_ptr_to_ctcb_ptr thread}"
                          in conseqPre)
                  apply (simp add: cong: option.case_cong)
                  apply (vcg exspec=deriveCap_modifies exspec=checkValidIPCBuffer_modifies)
                 apply (clarsimp simp: excaps_map_def Collect_const_mem ccHoarePost_def
                                       numeral_eqs
                                 cong: option.case_cong)
                 apply (frule interpret_excaps_eq[rule_format, where n=0], clarsimp)
                 apply (frule interpret_excaps_eq[rule_format, where n=1], clarsimp)
                 apply (frule interpret_excaps_eq[rule_format, where n=2], clarsimp)
                 apply (clarsimp simp: mask_def[where n=4] ccap_rights_relation_def
                                       rightsFromWord_wordFromRights capTCBPtr_eq
                                       ptr_val_tcb_ptr_mask2[unfolded mask_def objBits_defs, simplified]
                                       tcb_cnode_index_defs size_of_def
                                       option_to_0_def rf_sr_ksCurThread
                                       ThreadState_defs mask_eq_iff_w2p word_size
                                       from_bool_all_helper all_ex_eq_helper
                                       ucast_ucast_mask objBits_defs)
                 apply (subgoal_tac "args \<noteq> [] \<and> extraCaps \<noteq> []")
                  apply (simp add: word_sle_def cap_get_tag_isCap numeral_eqs
                                   hd_conv_nth hd_drop_conv_nth2
                                   word_FF_is_mask split_def
                                   thread_control_update_priority_def
                                   thread_control_update_mcp_def
                                   thread_control_update_space_def
                                   thread_control_update_ipc_buffer_def)
                  apply (auto split: option.split elim!: inl_inrE)[1]
                  apply (fastforce+)[2]
                apply clarsimp
                apply (strengthen if_n_updateCapData_valid_strg)
                apply (wp | wp (once) hoare_drop_imps)+
               apply (clarsimp simp: Collect_const_mem all_ex_eq_helper
                               cong: option.case_cong)
               apply vcg
              apply simp
              apply (wp | wp (once) hoare_drop_imps)+
             apply (simp add: Collect_const_mem all_ex_eq_helper)
             apply vcg
            apply simp
            apply (wp | wp (once) hoare_drop_imps)+
           apply (wpsimp | vcg exspec=getSyscallArg_modifies)+
  apply (clarsimp simp: Collect_const_mem all_ex_eq_helper)
  apply (rule conjI)
   apply (clarsimp simp: idButNot_def interpret_excaps_test_null
                         excaps_map_def neq_Nil_conv)
   apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt)
   apply (frule invs_mdb')
   apply (frule(2) tcb_at_capTCBPtr_CL)
   apply (rule conjI, fastforce)
   apply (drule interpret_excaps_eq)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_tcb_state'_def numeral_eqs le_ucast_ucast_le
                         tcb_at_invs' invs_valid_objs' invs_queues invs_sch_act_wf'
                         ct_in_state'_def pred_tcb_at'_def obj_at'_def tcb_st_refs_of'_def)
   apply (erule disjE; simp add: objBits_defs mask_def)
  apply (clarsimp simp: idButNot_def interpret_excaps_test_null
                        excaps_map_def neq_Nil_conv word_sle_def word_sless_def)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
  apply (frule interpret_excaps_eq[rule_format, where n=2], simp)
  apply (clarsimp simp: mask_def[where n=4] ccap_rights_relation_def
                        rightsFromWord_wordFromRights
                        capTCBPtr_eq tcb_ptr_to_ctcb_ptr_mask
                        tcb_cnode_index_defs size_of_def
                        option_to_0_def rf_sr_ksCurThread
                        ThreadState_defs mask_eq_iff_w2p word_size
                        from_bool_all_helper)
  apply (frule(1) tcb_at_h_t_valid [OF tcb_at_invs'])
  apply (clarsimp simp: typ_heap_simps numeral_eqs isCap_simps valid_cap'_def capAligned_def
                        objBits_simps)
  done

lemma not_isThreadCap_case:
  "\<lbrakk>\<not>isThreadCap cap\<rbrakk> \<Longrightarrow>
   (case cap of ThreadCap x \<Rightarrow> f x | _ \<Rightarrow> g) = g"
  by (clarsimp simp: isThreadCap_def split: capability.splits)

lemma decodeSetMCPriority_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps\<rbrakk> \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and valid_cap' cp and K (isThreadCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetMCPriority args cp extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetMCPriority_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: cap_' length___unsigned_long_' current_extra_caps_' buffer_' simp: decodeSetMCPriority_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac xf'=ret__int_' and R'=UNIV and R=\<top> and
                   val="from_bool (length args = 0 \<or> length extraCaps = 0)" in
                   ccorres_symb_exec_r_known_rv)
      apply vcg
      apply (force simp: interpret_excaps_test_null excaps_map_def from_bool_def unat_eq_0
                   split: bool.splits)
     apply ceqv
    apply clarsimp
    apply wpc
     (* Case args = [] *)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    (* Case args is Cons *)
    apply wpc
     (* Sub-case extraCaps = [] *)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    (* Main case where args and extraCaps are both Cons *)
    apply (rule ccorres_cond_false_seq)
    apply (simp add: split_def)
    apply (rule ccorres_add_return,
           ctac add: getSyscallArg_ccorres_foo'[where args=args and n=0 and buffer=buffer])
      apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
      apply (rule ccorres_move_c_guard_cte)
      apply ctac
        apply csymbr
        apply (simp add: cap_get_tag_isCap cong: call_ignore_cong)
        apply (rule ccorres_assert2)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_rhs_assoc)
         apply ccorres_rewrite
         apply (clarsimp simp: not_isThreadCap_case throwError_bind invocationCatch_def
                         simp del: id_simps)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (clarsimp simp: isCap_simps)
        apply csymbr
        apply csymbr
        (* Pre-conditions need to depend on the inner value of the thread cap *)
        apply (rule ccorres_inst[where P="Q (capTCBPtr (fst (extraCaps ! 0)))" and
                                       P'="Q' (capTCBPtr (fst (extraCaps ! 0)))" for Q Q'])
        apply (clarsimp simp: capTCBPtr_eq isCap_simps invocationCatch_use_injection_handler
                              injection_bindE[OF refl refl] bindE_assoc injection_handler_returnOk)
        apply (ctac add: ccorres_injection_handler_csum1[OF checkPrio_ccorres])
           apply (rule_tac P="hd args \<le> ucast (max_word :: priority)"
                           in ccorres_cross_over_guard_no_st)
           apply (simp add: ccorres_invocationCatch_Inr performInvocation_def)
           apply ccorres_rewrite
           apply (ctac add: setThreadState_ccorres)
             apply (simp add: invocationCatch_def)
             apply ccorres_rewrite
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply (ctac (no_vcg) add: invokeTCB_ThreadControl_ccorres)
               apply clarsimp
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE; simp)
              apply (rule ccorres_return_C_errorE; simp)
             apply wp
            apply (wpsimp wp: sts_invs_minor')
           apply simp
           apply (vcg exspec=setThreadState_modifies)
          apply simp
          apply (rename_tac err_c)
          apply (rule_tac P'="{s. err_c = errstate s}" in ccorres_from_vcg_split_throws)
           apply vcg
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: throwError_def return_def intr_and_se_rel_def syscall_error_rel_def)
         apply simp
         apply (rule injection_handler_wp)
         apply (rule checkPrio_wp[simplified validE_R_def])
        apply vcg
       apply (wp | simp | wpc | wp (once) hoare_drop_imps)+
      apply vcg
     apply wp
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: EXCEPTION_SYSCALL_ERROR_def EXCEPTION_NONE_def)
   apply vcg
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: ct_in_state'_def pred_tcb_at'
                         valid_cap'_def isCap_simps)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (clarsimp simp: maxPriority_def numPriorities_def FF_eq_minus_1)
   apply (rule conjI, clarsimp)
    apply (frule mcpriority_tcb_at'_prio_bounded, simp)
    apply (auto simp: valid_tcb_state'_def le_ucast_ucast_le
                elim!: obj_at'_weakenE pred_tcb'_weakenE
                dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: interpret_excaps_eq excaps_map_def)
  apply (simp add: ThreadState_defs mask_eq_iff_w2p word_size option_to_0_def)
  apply (frule rf_sr_ksCurThread)
  apply (simp only: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: valid_cap'_def capAligned_def interpret_excaps_eq excaps_map_def)
  apply (intro conjI impI allI)
   apply (clarsimp simp: unat_eq_0 le_max_word_ucast_id cap_get_tag_isCap_unfolded_H_cap isCap_simps)+
  done

lemma decodeSetPriority_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps\<rbrakk> \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and valid_cap' cp and K (isThreadCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetPriority args cp extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetPriority_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: cap_' length___unsigned_long_' current_extra_caps_' buffer_' simp: decodeSetPriority_def)
     apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac xf'=ret__int_' and R'=UNIV and R=\<top> and
                   val="from_bool (length args = 0 \<or> length extraCaps = 0)" in
                   ccorres_symb_exec_r_known_rv)
      apply vcg
      apply (force simp: interpret_excaps_test_null excaps_map_def from_bool_def unat_eq_0
                   split: bool.splits)
     apply ceqv
    apply clarsimp
    apply wpc
     (* Case args = [] *)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    (* Case args is Cons *)
    apply wpc
     (* Sub-case extraCaps = [] *)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    (* Main case where args and extraCaps are both Cons *)
    apply (rule ccorres_cond_false_seq)
    apply (simp add: split_def)
    apply (rule ccorres_add_return,
           ctac add: getSyscallArg_ccorres_foo'[where args=args and n=0 and buffer=buffer])
      apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
      apply (rule ccorres_move_c_guard_cte)
      apply ctac
        apply csymbr
        apply (simp add: cap_get_tag_isCap cong: call_ignore_cong)
        apply (rule ccorres_assert2)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_rhs_assoc)
         apply ccorres_rewrite
         apply (clarsimp simp: not_isThreadCap_case throwError_bind invocationCatch_def
                         simp del: id_simps)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (clarsimp simp: isCap_simps)
        apply csymbr
        apply csymbr
        (* Pre-conditions need to depend on the inner value of the thread cap *)
        apply (rule ccorres_inst[where P="Q (capTCBPtr (fst (extraCaps ! 0)))" and
                                       P'="Q' (capTCBPtr (fst (extraCaps ! 0)))" for Q Q'])
        apply (clarsimp simp: capTCBPtr_eq isCap_simps invocationCatch_use_injection_handler
                              injection_bindE[OF refl refl] bindE_assoc injection_handler_returnOk)
        apply (ctac add: ccorres_injection_handler_csum1[OF checkPrio_ccorres])
           apply (rule_tac P="hd args \<le> ucast (max_word :: priority)"
                           in ccorres_cross_over_guard_no_st)
           apply (simp add: ccorres_invocationCatch_Inr performInvocation_def)
           apply ccorres_rewrite
           apply (ctac add: setThreadState_ccorres)
             apply (simp add: invocationCatch_def)
             apply ccorres_rewrite
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply (ctac (no_vcg) add: invokeTCB_ThreadControl_ccorres)
               apply clarsimp
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE; simp)
              apply (rule ccorres_return_C_errorE; simp)
             apply wp
            apply (wpsimp wp: sts_invs_minor')
           apply simp
           apply (vcg exspec=setThreadState_modifies)
          apply simp
          apply (rename_tac err_c)
          apply (rule_tac P'="{s. err_c = errstate s}" in ccorres_from_vcg_split_throws)
           apply vcg
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: throwError_def return_def intr_and_se_rel_def syscall_error_rel_def)
         apply simp
         apply (rule injection_handler_wp)
         apply (rule checkPrio_wp[simplified validE_R_def])
        apply vcg
       apply (wp | simp | wpc | wp (once) hoare_drop_imps)+
      apply vcg
     apply wp
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: EXCEPTION_SYSCALL_ERROR_def EXCEPTION_NONE_def)
   apply vcg
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: ct_in_state'_def pred_tcb_at'
                         valid_cap'_def isCap_simps)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (clarsimp simp: maxPriority_def numPriorities_def FF_eq_minus_1)
   apply (rule conjI, clarsimp)
    apply (frule mcpriority_tcb_at'_prio_bounded, simp)
    apply (auto simp: valid_tcb_state'_def le_ucast_ucast_le
                elim!: obj_at'_weakenE pred_tcb'_weakenE
                dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: interpret_excaps_eq excaps_map_def)
  apply (simp add: ThreadState_defs mask_eq_iff_w2p word_size option_to_0_def)
  apply (frule rf_sr_ksCurThread)
  apply (simp only: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: valid_cap'_def capAligned_def interpret_excaps_eq excaps_map_def)
  apply (intro conjI impI allI)
   apply (clarsimp simp: unat_eq_0 le_max_word_ucast_id cap_get_tag_isCap_unfolded_H_cap isCap_simps)+
  done

lemma ucast_le_8_64_equiv:
  "x \<le> UCAST (8 \<rightarrow> 64) max_word \<Longrightarrow>
  (UCAST (64 \<rightarrow> 8) x \<le> y) = (x \<le> UCAST (8 \<rightarrow> 64) y)"
  apply (rule iffI)
   apply (word_bitwise; simp)
  apply (simp add: le_ucast_ucast_le)
  done

lemma mcpriority_tcb_at'_le_ucast:
  "pred_tcb_at' itcbMCP (\<lambda>mcp. x \<le> UCAST(8 \<rightarrow> 64) mcp) v s \<Longrightarrow>
   pred_tcb_at' itcbMCP (\<lambda>mcp. UCAST(64 \<rightarrow> 8) x \<le> mcp) v s"
  by (clarsimp simp: ucast_le_8_64_equiv mcpriority_tcb_at'_prio_bounded simp del: unsigned_uminus1)

lemma decodeSetSchedParams_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps\<rbrakk> \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and valid_cap' cp and K (isThreadCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetSchedParams args cp extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetSchedParams_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: cap_' length___unsigned_long_' current_extra_caps_' buffer_' simp: decodeSetSchedParams_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac xf'=ret__int_' and R'=UNIV and R=\<top> and
                   val="from_bool (length args < 2 \<or> length extraCaps = 0)" in
                   ccorres_symb_exec_r_known_rv)
      apply vcg
      apply (force simp: interpret_excaps_test_null excaps_map_def from_bool_def unat_eq_0
                         unat_arith_simps
                  split: bool.splits if_splits)
     apply ceqv
    apply clarsimp
(*
    apply (wpc)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (fastforce intro: syscall_error_throwError_ccorres_n simp: syscall_error_to_H_cases)
    apply (wpc)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (fastforce intro: syscall_error_throwError_ccorres_n simp: syscall_error_to_H_cases)
    apply (wpc)
     apply (rule ccorres_cond_true_seq)
     apply (clarsimp simp: throwError_bind invocationCatch_def)
     apply (rule ccorres_rhs_assoc)
     apply (ccorres_rewrite)
     apply (fastforce intro: syscall_error_throwError_ccorres_n simp: syscall_error_to_H_cases)
*)
    apply (wpc,
           rule ccorres_cond_true_seq,
           clarsimp simp: throwError_bind invocationCatch_def,
           rule ccorres_rhs_assoc,
           ccorres_rewrite,
           fastforce intro: syscall_error_throwError_ccorres_n simp: syscall_error_to_H_cases)+
    (* Main case where args and extraCaps are both well-formed *)
    apply (rule ccorres_cond_false_seq)
    apply (simp add: split_def)
    apply (rule ccorres_add_return,
           ctac add: getSyscallArg_ccorres_foo'[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return,
             ctac add: getSyscallArg_ccorres_foo'[where args=args and n=1 and buffer=buffer])
        apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
        apply (rule ccorres_move_c_guard_cte)
        apply ctac
          apply csymbr
          apply (simp add: cap_get_tag_isCap cong: call_ignore_cong)
          apply (rule ccorres_assert2)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (rule ccorres_rhs_assoc)
           apply ccorres_rewrite
           apply (clarsimp simp: not_isThreadCap_case throwError_bind invocationCatch_def
                           simp del: id_simps)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: isCap_simps)
          apply csymbr
          apply csymbr
          (* Pre-conditions need to depend on the inner value of the thread cap *)
          apply (rule ccorres_inst[where P="Q (capTCBPtr (fst (extraCaps ! 0)))" and
                                         P'="Q' (capTCBPtr (fst (extraCaps ! 0)))" for Q Q'])
          apply (clarsimp simp: capTCBPtr_eq isCap_simps invocationCatch_use_injection_handler
                                injection_bindE[OF refl refl] bindE_assoc injection_handler_returnOk)
          apply (ctac add: ccorres_injection_handler_csum1[OF checkPrio_ccorres])
             apply (rule_tac P="args ! 0 \<le> ucast (max_word :: priority)"
                             in ccorres_cross_over_guard_no_st)
             apply (simp add: ccorres_invocationCatch_Inr performInvocation_def)
             apply ccorres_rewrite
             apply (clarsimp simp: capTCBPtr_eq isCap_simps invocationCatch_use_injection_handler
                                   injection_bindE[OF refl refl] bindE_assoc injection_handler_returnOk)
             apply (ctac add: ccorres_injection_handler_csum1[OF checkPrio_ccorres])
                apply (rule_tac P="args ! 1 \<le> ucast (max_word :: priority)"
                                in ccorres_cross_over_guard_no_st)
                apply (simp add: ccorres_invocationCatch_Inr performInvocation_def)
                apply ccorres_rewrite
                apply (ctac add: setThreadState_ccorres)
                  apply (simp add: invocationCatch_def)
                  apply ccorres_rewrite
                  apply csymbr
                  apply csymbr
                  apply csymbr
                  apply csymbr
                  apply (ctac (no_vcg) add: invokeTCB_ThreadControl_ccorres)
                    apply clarsimp
                    apply (rule ccorres_alternative2)
                    apply (rule ccorres_return_CE; simp)
                   apply (rule ccorres_return_C_errorE; simp)
                  apply wp
                 apply (wpsimp wp: sts_invs_minor')
                apply simp
                apply (vcg exspec=setThreadState_modifies)
               apply simp
               apply (rename_tac err_c)
               apply (rule_tac P'="{s. err_c = errstate s}" in ccorres_from_vcg_split_throws)
                apply vcg
               apply (rule conseqPre, vcg)
               apply (clarsimp simp: throwError_def return_def intr_and_se_rel_def syscall_error_rel_def)
              apply simp
              apply (rule injection_handler_wp)
              apply (rule checkPrio_wp[simplified validE_R_def])
             apply vcg
            apply clarsimp
            apply ccorres_rewrite
            apply (rule ccorres_return_C_errorE; simp)
           apply simp
           apply (rule injection_handler_wp)
           apply (rule checkPrio_wp[simplified validE_R_def])
          apply vcg
         apply (wp | simp | wpc | wp (once) hoare_drop_imps)+
        apply vcg
       apply simp
       apply (rule return_wp)
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
     apply (rule return_wp)
    apply simp
    apply (vcg exspec=getSyscallArg_modifies)
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: ct_in_state'_def pred_tcb_at'
      valid_cap'_def isCap_simps)
   apply (rule conjI; clarsimp simp: sysargs_rel_to_n n_msgRegisters_def)
   apply (clarsimp simp: maxPriority_def numPriorities_def FF_eq_minus_1)
   apply (rule conjI, clarsimp)
    apply (insert mcpriority_tcb_at'_prio_bounded[where prio="args ! 0"])
    apply (insert mcpriority_tcb_at'_prio_bounded[where prio="args ! 1"])
    apply (auto simp: valid_tcb_state'_def mcpriority_tcb_at'_le_ucast
                elim!: obj_at'_weakenE pred_tcb'_weakenE
                dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: interpret_excaps_eq excaps_map_def)
  apply (simp add: ThreadState_defs mask_eq_iff_w2p word_size option_to_0_def)
  apply (frule rf_sr_ksCurThread)
  apply (simp only: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: valid_cap'_def capAligned_def interpret_excaps_eq excaps_map_def)
  apply (intro conjI impI allI)
                      by (clarsimp simp: unat_eq_0 le_max_word_ucast_id
                                         thread_control_update_mcp_def thread_control_update_priority_def
                                         cap_get_tag_isCap_unfolded_H_cap isCap_simps
                                         interpret_excaps_eq excaps_map_def)+

lemma decodeSetIPCBuffer_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp and cte_at' slot and K (isThreadCap cp)
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. slot_' s = cte_Ptr slot}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetIPCBuffer args cp slot extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetIPCBuffer_'proc)"
  apply (cinit' lift: cap_' length___unsigned_long_' slot_' current_extra_caps_' buffer_'
                simp: decodeSetIPCBuffer_def)
   apply wpc
    apply (simp add: unat_eq_0)
    apply csymbr
    apply simp
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (clarsimp simp: throwError_def return_def
                          intr_and_se_rel_def exception_defs
                          syscall_error_rel_def syscall_error_to_H_cases)
   apply csymbr
   apply (rule ccorres_cond_false_seq)
   apply csymbr
   apply (simp del: Collect_const)
   apply (simp add: interpret_excaps_test_null excaps_map_Nil if_1_0_0
               del: Collect_const)
   apply wpc
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_cond_false_seq)
   apply (simp add: split_def
               del: Collect_const)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo [where args=args and n=0 and buffer=buffer])
     apply csymbr
     apply (rule ccorres_move_c_guard_cte)
     apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
     apply ctac
       apply (rule ccorres_assert2)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: returnOk_bind ccorres_invocationCatch_Inr performInvocation_def)
        apply csymbr
        apply (ctac add: setThreadState_ccorres)
          apply csymbr
          apply csymbr
          apply csymbr
          apply (ctac add: invokeTCB_ThreadControl_ccorres)
             apply simp
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_return_C_errorE, simp+)[1]
           apply wp
          apply (vcg exspec=invokeTCB_ThreadControl_modifies)
         apply simp
         apply (wp sts_invs_minor')
        apply (vcg exspec=setThreadState_modifies)
       apply (simp add: bindE_assoc del: Collect_const)
       apply (rule ccorres_rhs_assoc)+
       apply (csymbr, csymbr)
       apply (simp add: bindE_bind_linearise)
       apply (rule ccorres_split_nothrow_case_sum)
            apply (ctac add: deriveCap_ccorres)
           apply ceqv
          apply (simp add: Collect_False del: Collect_const)
          apply csymbr
          apply (rule ccorres_split_nothrow_case_sum)
               apply (ctac add: checkValidIPCBuffer_ccorres)
              apply ceqv
             apply (simp add: Collect_False returnOk_bind
                              ccorres_invocationCatch_Inr
                         del: Collect_const)
             apply (ctac add: setThreadState_ccorres)
               apply (simp add: performInvocation_def)
               apply (csymbr, csymbr, csymbr)
               apply (ctac add: invokeTCB_ThreadControl_ccorres)
                  apply simp
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_return_C_errorE, simp+)[1]
                apply wp
               apply (vcg exspec=invokeTCB_ThreadControl_modifies)
              apply simp
              apply (wp sts_invs_minor')
             apply (simp add: Collect_const_mem cintr_def intr_and_se_rel_def)
             apply (vcg exspec=setThreadState_modifies)
            apply (simp add: invocationCatch_def)
            apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
            apply vcg
           apply simp
           apply (wp checkValidIPCBuffer_ArchObject_wp)
          apply (simp add: intr_and_se_rel_def syscall_error_rel_def
                           exception_defs)
          apply (vcg exspec=checkValidIPCBuffer_modifies)
         apply (simp add: invocationCatch_def)
         apply (rule ccorres_split_throws)
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply vcg
        apply simp
        apply (wp | wp (once) hoare_drop_imps)+
       apply (simp add: Collect_const_mem)
       apply (vcg exspec=deriveCap_modifies)
      apply simp
      apply (wp | wp (once) hoare_drop_imps)+
     apply simp
     apply vcg
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: Collect_const_mem if_1_0_0 ct_in_state'_def
                        pred_tcb_at' cintr_def intr_and_se_rel_def
                        exception_defs syscall_error_rel_def)
  apply (rule conjI)
   apply (clarsimp simp: excaps_in_mem_def slotcap_in_mem_def)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (frule invs_mdb')
   apply (frule(2) tcb_at_capTCBPtr_CL)
   apply (auto simp: isCap_simps valid_cap'_def valid_mdb'_def valid_tcb_state'_def
                     valid_mdb_ctes_def no_0_def excaps_map_def
               elim: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread'
              dest!: interpret_excaps_eq)[1]
  apply (clarsimp simp: option_to_0_def rf_sr_ksCurThread word_sless_def word_sle_def mask_def)
  apply (rule conjI[rotated], clarsimp+)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp add: excaps_map_Nil)
  apply (simp add: mask_def ThreadState_defs excaps_map_def)
  apply (clarsimp simp: ccap_rights_relation_def rightsFromWord_wordFromRights
                        cap_get_tag_isCap)
  apply (frule cap_get_tag_to_H, subst cap_get_tag_isCap, assumption, assumption)
  apply clarsimp
  done

lemma bindNTFN_alignment_junk:
  "\<lbrakk> is_aligned tcb tcbBlockSizeBits; bits \<le> ctcb_size_bits \<rbrakk>
    \<Longrightarrow> ptr_val (tcb_ptr_to_ctcb_ptr tcb) && ~~ mask bits = ptr_val (tcb_ptr_to_ctcb_ptr tcb)"
  apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def projectKOs)
  apply (rule is_aligned_neg_mask_eq)
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   by (auto simp add: is_aligned_def objBits_defs ctcb_offset_defs)

lemma option_to_ctcb_ptr_canonical:
  "\<lbrakk>pspace_canonical' s; tcb_at' tcb s\<rbrakk> \<Longrightarrow>
     option_to_ctcb_ptr (Some tcb) = tcb_Ptr (sign_extend 47 (ptr_val (tcb_ptr_to_ctcb_ptr tcb)))"
  apply (clarsimp simp: option_to_ctcb_ptr_def)
  apply (frule (1) obj_at'_is_canonical)
  by (fastforce dest: canonical_address_tcb_ptr
                simp: obj_at'_def objBits_simps' projectKOs canonical_address_sign_extended
                      sign_extended_iff_sign_extend)

lemma bindNotification_ccorres:
  "ccorres dc xfdc (invs' and tcb_at' tcb)
    (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tcb}
          \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr}) []
   (bindNotification tcb ntfnptr)
   (Call bindNotification_'proc)"
  apply (cinit lift: tcb_' ntfnPtr_' simp: bindNotification_def)
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule_tac P="invs' and ko_at' ntfn ntfnptr and tcb_at' tcb" and P'=UNIV
                    in ccorres_split_nothrow_novcg)
        apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp)
        apply (frule cmap_relation_ntfn)
        apply (erule (1) cmap_relation_ko_atE)
        apply (rule conjI)
         apply (erule h_t_valid_clift)
        apply (clarsimp simp: setNotification_def split_def)
        apply (rule bexI [OF _ setObject_eq])
            apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                                    cpspace_relation_def update_ntfn_map_tos
                                    typ_heap_simps')
            apply (elim conjE)
            apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
              apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
               apply (clarsimp simp: cnotification_relation_def Let_def
                                     mask_def [where n=2] NtfnState_Waiting_def)
               apply (case_tac "ntfnObj ntfn")
                 apply ((clarsimp simp: option_to_ctcb_ptr_canonical[OF invs_pspace_canonical'])+)[3]
              apply (auto simp: option_to_ctcb_ptr_def objBits_simps'
                                bindNTFN_alignment_junk)[1]
             apply (simp add: carch_state_relation_def fpu_null_state_heap_update_tag_disj_simps
                              global_ioport_bitmap_heap_update_tag_disj_simps)
            apply (simp add: cmachine_state_relation_def)
           apply (simp add: h_t_valid_clift_Some_iff)
          apply (simp add: objBits_simps')
         apply (simp add: objBits_simps)
        apply assumption
       apply ceqv
      apply (rule ccorres_move_c_guard_tcb)
      apply (simp add: setBoundNotification_def)
      apply (rule_tac P'=\<top> and P=\<top> in threadSet_ccorres_lemma3)
       apply vcg
      apply simp
      apply (erule (1) rf_sr_tcb_update_no_queue2,
        (simp add: typ_heap_simps')+, simp_all?)[1]
      apply (simp add: ctcb_relation_def option_to_ptr_def option_to_0_def)
     apply simp
     apply (wp get_ntfn_ko'| simp add: guard_is_UNIV_def)+
  done

lemma invokeTCB_NotificationControl_bind_ccorres:
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
    (invs' and tcb_inv_wf' (tcbinvocation.NotificationControl t (Some a)))
    (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr t} \<inter> {s. ntfnPtr_' s = ntfn_Ptr a}) []
    (invokeTCB (tcbinvocation.NotificationControl t (Some a)))
    (Call invokeTCB_NotificationControl_'proc)"
  apply (cinit lift: tcb_' ntfnPtr_')
   apply (clarsimp simp: option_to_0_def liftE_def)
   apply (rule ccorres_cond_true_seq)
   apply (ctac(no_vcg) add: bindNotification_ccorres)
    apply (rule ccorres_return_CE[unfolded returnOk_def, simplified])
      apply simp
     apply simp
    apply simp
   apply wp
  apply (case_tac "a = 0", auto)
  done

lemma invokeTCB_NotificationControl_unbind_ccorres:
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
    (invs' and tcb_inv_wf' (tcbinvocation.NotificationControl t None))
    (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr t} \<inter> {s. ntfnPtr_' s = NULL}) []
    (invokeTCB (tcbinvocation.NotificationControl t None))
    (Call invokeTCB_NotificationControl_'proc)"
  apply (cinit lift: tcb_' ntfnPtr_')
   apply (clarsimp simp add: option_to_0_def liftE_def)
   apply (ctac(no_vcg) add: unbindNotification_ccorres)
    apply (rule ccorres_return_CE[unfolded returnOk_def, simplified])
      apply simp
     apply simp
    apply simp
   apply wp
  apply (clarsimp simp: option_to_0_def)
  done

lemma valid_objs_boundNTFN_NULL:
  "ko_at' tcb p s ==> valid_objs' s \<Longrightarrow> no_0_obj' s \<Longrightarrow> tcbBoundNotification tcb \<noteq> Some 0"
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: valid_tcb'_def projectKOs valid_obj'_def)
  done

lemma decodeUnbindNotification_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp and K (isThreadCap cp)
              and tcb_at' (capTCBPtr cp)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s))
       (UNIV \<inter> {s. ccap_relation cp (cap_' s)}) []
     (decodeUnbindNotification cp >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeUnbindNotification_'proc)"
  apply (cinit' lift: cap_' simp: decodeUnbindNotification_def)
   apply csymbr
   apply csymbr
   apply (rule ccorres_Guard_Seq)
   apply (simp add: liftE_bindE bind_assoc)
   apply (rule ccorres_pre_getBoundNotification)
   apply (rule_tac P="\<lambda>s. ntfn \<noteq> Some 0" in ccorres_cross_over_guard)
   apply (simp add: bindE_bind_linearise)
   apply wpc
    apply (simp add: bindE_bind_linearise[symmetric]
                     injection_handler_throwError
                     invocationCatch_use_injection_handler)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                         syscall_error_to_H_cases exception_defs)
   apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                     performInvocation_def)
   apply (rule ccorres_cond_false_seq)
   apply simp
   apply (ctac add: setThreadState_ccorres)
     apply (ctac add: invokeTCB_NotificationControl_unbind_ccorres)
        apply simp
        apply (rule ccorres_alternative2)
        apply (rule ccorres_return_CE, simp+)[1]
       apply (rule ccorres_return_C_errorE, simp+)[1]
      apply wp
     apply (vcg exspec=invokeTCB_NotificationControl_modifies)
    apply simp
    apply (wp sts_invs_minor' hoare_case_option_wp sts_bound_tcb_at' | wpc | simp)+
   apply (vcg exspec=setThreadState_modifies)
  apply (clarsimp, frule obj_at_ko_at', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_tcb], assumption)
   apply (erule ko_at_projectKO_opt)
  apply (clarsimp simp: isCap_simps)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (auto simp: ctcb_relation_def typ_heap_simps cap_get_tag_ThreadCap ct_in_state'_def
                    option_to_ptr_def option_to_0_def ThreadState_defs
                    mask_def rf_sr_ksCurThread valid_tcb_state'_def
             elim!: pred_tcb'_weakenE
             dest!: valid_objs_boundNTFN_NULL)
  done

lemma nTFN_case_If_ptr:
  "(case x of capability.NotificationCap a b c d \<Rightarrow> P a d | _ \<Rightarrow> Q) = (if (isNotificationCap x) then P (capNtfnPtr x) (capNtfnCanReceive x) else Q)"
  by (auto simp: isNotificationCap_def split: capability.splits)

lemma decodeBindNotification_ccorres:
  notes prod.case_cong_weak[cong]
        option.case_cong_weak[cong]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp
              and tcb_at' (capTCBPtr cp) and ex_nonz_cap_to' (capTCBPtr cp)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v). ex_nonz_cap_to' y s )
              and (excaps_in_mem extraCaps o ctes_of)
              and K (isThreadCap cp))
       (UNIV \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}) []
     (decodeBindNotification cp extraCaps >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeBindNotification_'proc)"
  using [[goals_limit=1]]
  apply (simp, rule ccorres_gen_asm)
  apply (cinit' lift: cap_' current_extra_caps_' simp: decodeBindNotification_def)
   apply (simp add: bind_assoc whenE_def bind_bindE_assoc interpret_excaps_test_null
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: excaps_map_def invocationCatch_def throwError_bind null_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: excaps_map_def null_def del: Collect_const cong: call_ignore_cong)
   apply csymbr
   apply csymbr
   apply (rule ccorres_Guard_Seq)
   apply (simp add: liftE_bindE bind_assoc cong: call_ignore_cong)
   apply (rule ccorres_pre_getBoundNotification)
   apply (rule_tac P="\<lambda>s. rv \<noteq> Some 0" in ccorres_cross_over_guard)
   apply (simp add: bindE_bind_linearise cong: call_ignore_cong)
   apply wpc
    prefer 2
    apply (simp add: bindE_bind_linearise[symmetric] injection_handler_throwError
                     invocationCatch_use_injection_handler throwError_bind invocationCatch_def)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases
                          exception_defs)
   apply (simp add: returnOk_bind ccorres_invocationCatch_Inr performInvocation_def
                    bindE_bind_linearise[symmetric] cong: call_ignore_cong)
   apply (rule ccorres_cond_false_seq)
   apply (simp cong: call_ignore_cong)
   apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
   apply (rule ccorres_move_c_guard_cte)
   apply ctac
     apply csymbr
     apply (simp add: cap_get_tag_isCap if_1_0_0 del: Collect_const cong: call_ignore_cong)
     apply (rule ccorres_assert2)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (rule_tac P="Q (capNtfnPtr rva) (capNtfnCanReceive rva) rva"for Q in ccorres_inst)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (simp add: hd_conv_nth del: Collect_const cong: call_ignore_cong)
      apply (simp only: cap_get_tag_isCap(3)[symmetric] cong: call_ignore_cong, frule(1) cap_get_tag_to_H(3) )
      apply (simp add: case_bool_If if_to_top_of_bindE if_to_top_of_bind bind_assoc
                  del: Collect_const cong: if_cong call_ignore_cong)
      apply csymbr
      apply (clarsimp simp add: if_to_top_of_bind to_bool_eq_0[symmetric] simp del: Collect_const)
      apply (rule ccorres_Cond_rhs_Seq)
       apply (clarsimp simp: throwError_bind invocationCatch_def)
       apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
        apply vcg
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases exception_defs)
      apply (clarsimp simp: to_bool_def)
      apply (rule ccorres_pre_getNotification)
      apply (rename_tac ntfn)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac xf'="ret__int_'" and val="from_bool (ntfnBoundTCB ntfn \<noteq> None \<or>
                                                    isWaitingNtfn (ntfnObj ntfn))"
                                       and R="ko_at' ntfn (capNtfnPtr_CL (cap_notification_cap_lift ntfn_cap))
                                                  and valid_ntfn' ntfn"
                                       and R'=UNIV
                                  in  ccorres_symb_exec_r_known_rv_UNIV)
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: if_1_0_0)

         apply (erule cmap_relationE1[OF cmap_relation_ntfn], erule ko_at_projectKO_opt)
         apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def
                               valid_ntfn'_def)
         apply (case_tac "ntfnObj ntfn", simp_all add: isWaitingNtfn_def option_to_ctcb_ptr_def
                                                split: option.split_asm if_split,
                         auto simp: neq_Nil_conv tcb_queue_relation'_def tcb_at_not_NULL[symmetric]
                                    tcb_at_not_NULL)[1]
        apply ceqv
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
       apply (simp add: bindE_bind_linearise del: Collect_const)
       apply wpc
         \<comment> \<open>IdleNtfn\<close>
         apply (simp add: case_option_If del: Collect_const)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0)
          apply (simp add: bindE_bind_linearise[symmetric] injection_handler_throwError
                           invocationCatch_use_injection_handler throwError_bind invocationCatch_def)
          apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
           apply vcg
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                syscall_error_to_H_cases exception_defs)
         apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0 returnOk_bind)
         apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0 returnOk_bind
                               ccorres_invocationCatch_Inr performInvocation_def)
         apply (ctac add: setThreadState_ccorres)
           apply (ctac add: invokeTCB_NotificationControl_bind_ccorres)
              apply simp
              apply (rule ccorres_alternative2)
              apply (rule ccorres_return_CE, simp+)[1]
             apply (rule ccorres_return_C_errorE, simp+)[1]
            apply wp
           apply (vcg exspec=invokeTCB_NotificationControl_modifies)
          apply simp
          apply (wp sts_invs_minor' hoare_case_option_wp sts_bound_tcb_at' | wpc | simp)+
         apply (vcg exspec=setThreadState_modifies)
        apply (simp add: case_option_If del: Collect_const)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0)
         apply (simp add: bindE_bind_linearise[symmetric] injection_handler_throwError
                          invocationCatch_use_injection_handler throwError_bind invocationCatch_def)
         apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
          apply vcg
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                               syscall_error_to_H_cases exception_defs)
        apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0 returnOk_bind)
        apply (clarsimp simp: isWaitingNtfn_def from_bool_neq_0 returnOk_bind
                              ccorres_invocationCatch_Inr performInvocation_def)
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: invokeTCB_NotificationControl_bind_ccorres)
             apply simp
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_return_C_errorE, simp+)[1]
           apply wp
          apply (vcg exspec=invokeTCB_NotificationControl_modifies)
         apply simp
         apply (wp sts_invs_minor' hoare_case_option_wp sts_bound_tcb_at' | wpc | simp)+
        apply (vcg exspec=setThreadState_modifies)
       apply (simp add: bindE_bind_linearise[symmetric] injection_handler_throwError
                        invocationCatch_use_injection_handler throwError_bind invocationCatch_def)
       apply (rule ccorres_cond_true_seq)
       apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
        apply vcg
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                             syscall_error_to_H_cases exception_defs)
      apply (clarsimp simp add: guard_is_UNIV_def isWaitingNtfn_def
                                ThreadState_defs mask_def
                                rf_sr_ksCurThread capTCBPtr_eq)
     apply (simp add: hd_conv_nth bindE_bind_linearise nTFN_case_If_ptr throwError_bind invocationCatch_def)
     apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
      apply vcg
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases
                           exception_defs)
    apply clarsimp
    apply (wp | simp | wpc | wp (once) hoare_drop_imps)+
   apply vcg
  apply clarsimp
  apply (rule conjI)
   apply safe[1]
                  apply (fastforce simp: invs'_def valid_state'_def valid_pspace'_def
                                  dest!: valid_objs_boundNTFN_NULL)
                 apply ((fastforce elim!: pred_tcb'_weakenE obj_at'_weakenE
                                    simp: ct_in_state'_def from_bool_0 isCap_simps excaps_map_def
                                          neq_Nil_conv obj_at'_def pred_tcb_at'_def valid_tcb_state'_def)+)[12]
     apply (clarsimp dest!: obj_at_valid_objs'[OF _ invs_valid_objs']
                      simp: projectKOs valid_obj'_def)
    apply (clarsimp simp: excaps_map_Nil cte_wp_at_ctes_of excaps_map_def neq_Nil_conv
                   dest!: interpret_excaps_eq )
   apply (clarsimp simp: excaps_map_Nil)
  apply (frule obj_at_ko_at', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_tcb], assumption)
   apply (erule ko_at_projectKO_opt)
  apply (clarsimp simp: isCap_simps)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply safe[1]
         apply (clarsimp simp: typ_heap_simps excaps_map_def neq_Nil_conv
                        dest!: interpret_excaps_eq)
        apply clarsimp
        apply (frule cap_get_tag_isCap_unfolded_H_cap(3))
        apply (clarsimp simp: typ_heap_simps cap_get_tag_ThreadCap ccap_relation_def)
       apply (auto simp: word_sless_alt typ_heap_simps cap_get_tag_ThreadCap ctcb_relation_def
                         option_to_ptr_def option_to_0_def
                  split: if_split)
  done


lemma decodeSetSpace_ccorres:
  notes tl_drop_1[simp] scast_mask_8 [simp]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp and cte_at' slot and K (isThreadCap cp)
              and tcb_at' (capTCBPtr cp)
              and (\<lambda>s. \<forall>rf \<in> zobj_refs' cp. ex_nonz_cap_to' rf s)
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. slot_' s = cte_Ptr slot}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetSpace args cp slot extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetSpace_'proc)"
  supply unsigned_numeral[simp del]
  apply (cinit' lift: cap_' length___unsigned_long_' slot_' current_extra_caps_' buffer_'
                simp: decodeSetSpace_def)
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: if_1_0_0)
    apply (rule ccorres_cond_true_seq | simp)+
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (subgoal_tac "unat length___unsigned_long < 3")
     apply (clarsimp simp: throwError_def invocationCatch_def fst_return
                           intr_and_se_rel_def syscall_error_rel_def
                           syscall_error_to_H_cases exception_defs
                           subset_iff
                    split: list.split)
    apply unat_arith
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: if_1_0_0 interpret_excaps_test_null excaps_map_Nil)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
    apply (clarsimp simp: throwError_def invocationCatch_def fst_return
                          intr_and_se_rel_def syscall_error_rel_def
                          syscall_error_to_H_cases exception_defs
                   split: list.split)
   apply csymbr
   apply (simp add: if_1_0_0 interpret_excaps_test_null del: Collect_const)
   apply (rule_tac P="\<lambda>c. ccorres rvr xf P P' hs a (Cond c c1 c2 ;; c3)" for rvr xf P P' hs a c1 c2 c3 in ssubst)
    apply (rule Collect_cong)
    apply (rule interpret_excaps_test_null)
     apply (clarsimp simp: neq_Nil_conv)
    apply simp
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
    apply (clarsimp simp: throwError_def invocationCatch_def fst_return
                          intr_and_se_rel_def syscall_error_rel_def
                          syscall_error_to_H_cases exception_defs
                          excaps_map_def
                   split: list.split)
   apply (clarsimp simp add: linorder_not_less word_le_nat_alt
                             excaps_map_Nil length_excaps_map
                   simp del: Collect_const)
   apply (drule_tac a="Suc 0" in neq_le_trans [OF not_sym])
    apply (clarsimp simp: neq_Nil_conv)
   apply (rule_tac P="\<lambda>a. ccorres rvr xf P P' hs a c" for rvr xf P P' hs c in ssubst,
          rule bind_cong [OF _ refl], rule list_case_helper,
          clarsimp)+
   apply (simp add: hd_drop_conv_nth2 del: Collect_const)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return,
            ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_add_return,
              ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
         apply csymbr
         apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
         apply (rule ccorres_move_c_guard_cte)
         apply ctac
           apply (rule ccorres_assert2)
           apply csymbr
           apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=1])
           apply (rule ccorres_move_c_guard_cte)
           apply ctac
             apply (rule ccorres_assert2)
             apply csymbr
             apply (simp add: decodeSetSpace_def injection_bindE[OF refl]
                              split_def
                              tcb_cnode_index_defs[THEN ptr_add_assertion_positive[OF ptr_add_assertion_positive_helper]]
                         del: Collect_const)
             apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq
                         ccorres_rhs_assoc)+
             apply (simp add: injection_liftE[OF refl] bindE_assoc
                              liftM_def getThreadCSpaceRoot
                              getThreadVSpaceRoot del: Collect_const)
             apply (simp add: liftE_bindE bind_assoc del: Collect_const)
             apply (ctac add: slotCapLongRunningDelete_ccorres)
               apply (rule ccorres_move_array_assertion_tcb_ctes)
               apply (simp del: Collect_const)
               apply csymbr
               apply (clarsimp simp add: if_1_0_0 from_bool_0
                               simp del: Collect_const)
               apply (rule ccorres_Cond_rhs_Seq)
                apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_slotCapLongRunningDelete])
                  apply (simp add: unlessE_def throwError_bind invocationCatch_def
                             cong: StateSpace.state.fold_congs globals.fold_congs)
                  apply (rule ccorres_cond_true_seq)
                  apply (rule syscall_error_throwError_ccorres_n)
                  apply (simp add: syscall_error_to_H_cases)
                 apply wp+
               apply (rule ccorres_rhs_assoc)+
               apply csymbr
              apply (simp add: tcb_cnode_index_defs[THEN ptr_add_assertion_positive[OF ptr_add_assertion_positive_helper]]
                          del: Collect_const)
              apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_Guard_Seq
                          ccorres_rhs_assoc)+
               apply (ctac add: slotCapLongRunningDelete_ccorres)
                 apply (rule ccorres_move_array_assertion_tcb_ctes)
                 apply (simp del: Collect_const)
                 apply csymbr
                 apply (clarsimp simp add: if_1_0_0 from_bool_0
                                 simp del: Collect_const)
                 apply (rule ccorres_Cond_rhs_Seq)
                  apply (simp add: unlessE_def throwError_bind invocationCatch_def
                             cong: StateSpace.state.fold_congs globals.fold_congs)
                  apply (rule syscall_error_throwError_ccorres_n)
                  apply (simp add: syscall_error_to_H_cases)
                 apply (simp add: unlessE_def
                             del: Collect_const)
                 apply (rule ccorres_add_return,
                        rule_tac r'="\<lambda>rv rv'. ccap_relation (if args ! Suc 0 = 0 then fst (hd extraCaps)
                                           else updateCapData False (args ! Suc 0) (fst (hd extraCaps))) rv'"
                             and xf'="cRootCap_'" in ccorres_split_nothrow)
                     apply (rule_tac P'="{s. cRootCap = cRootCap_' s}"
                                 in ccorres_from_vcg[where P=\<top>])
                     apply (rule allI, rule conseqPre, vcg)
                     apply (subgoal_tac "extraCaps \<noteq> []")
                      apply (clarsimp simp: returnOk_def return_def hd_conv_nth)
                      apply fastforce
                     apply clarsimp
                    apply ceqv
                   apply (simp add: invocationCatch_use_injection_handler
                                    injection_bindE [OF refl refl] bindE_assoc
                               del: Collect_const)
                   apply (ctac add: ccorres_injection_handler_csum1
                                              [OF deriveCap_ccorres])
                      apply (simp add: Collect_False del: Collect_const)
                      apply csymbr
                      apply csymbr
                      apply (simp add: cnode_cap_case_if cap_get_tag_isCap
                                  del: Collect_const)
                      apply (rule ccorres_Cond_rhs_Seq)
                       apply (simp add: injection_handler_throwError
                                  cong: StateSpace.state.fold_congs globals.fold_congs)
                       apply (rule syscall_error_throwError_ccorres_n)
                       apply (simp add: syscall_error_to_H_cases)
                      apply (simp add: injection_handler_returnOk del: Collect_const)
                      apply (rule ccorres_add_return,
                             rule_tac r'="\<lambda>rv rv'. ccap_relation (if args ! 2 = 0 then fst (extraCaps ! Suc 0)
                                                else updateCapData False (args ! 2) (fst (extraCaps ! Suc 0))) rv'"
                                  and xf'="vRootCap_'" in ccorres_split_nothrow)
                           apply (rule_tac P'="{s. vRootCap = vRootCap_' s}"
                                  in ccorres_from_vcg[where P=\<top>])
                           apply (rule allI, rule conseqPre, vcg)
                           apply (clarsimp simp: returnOk_def return_def hd_drop_conv_nth2)
                           apply fastforce
                          apply ceqv
                         apply (ctac add: ccorres_injection_handler_csum1
                                             [OF deriveCap_ccorres])
                            apply (simp add: Collect_False del: Collect_const)
                            apply csymbr
                            apply csymbr
                            apply (simp add: from_bool_0 isValidVTableRoot_conv del: Collect_const)
                            apply (rule ccorres_Cond_rhs_Seq)
                             apply (simp add: injection_handler_throwError
                                        cong: StateSpace.state.fold_congs globals.fold_congs)
                             apply (rule syscall_error_throwError_ccorres_n)
                             apply (simp add: syscall_error_to_H_cases)
                            apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                             performInvocation_def)
                            apply (ctac add: setThreadState_ccorres)
                              apply csymbr
                              apply csymbr
                              apply (ctac(no_vcg) add: invokeTCB_ThreadControl_ccorres)
                                apply simp
                                apply (rule ccorres_alternative2)
                                apply (rule ccorres_return_CE, simp+)[1]
                               apply (rule ccorres_return_C_errorE, simp+)[1]
                              apply wp
                             apply simp
                             apply (wp sts_invs_minor')
                            apply (vcg exspec=setThreadState_modifies)
                           apply simp
                           apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
                           apply vcg
                          apply simp
                          apply (wp hoare_drop_imps)
                         apply (wp injection_wp_E [OF refl])
                        apply (simp add: Collect_const_mem cintr_def intr_and_se_rel_def
                                         all_ex_eq_helper syscall_error_rel_def
                                         exception_defs)
                        apply (vcg exspec=deriveCap_modifies)
                       apply (simp cong: if_cong)
                       apply wp
                      apply (simp add: Collect_const_mem all_ex_eq_helper)
                      apply vcg
                     apply simp
                     apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
                     apply vcg
                    apply (simp cong: if_cong)
                    apply (wp hoare_drop_imps injection_wp_E[OF refl])
                   apply (simp add: Collect_const_mem all_ex_eq_helper
                                    numeral_eqs syscall_error_rel_def
                                    exception_defs cintr_def intr_and_se_rel_def)
                   apply (vcg exspec=deriveCap_modifies)
                  apply (simp cong: if_cong)
                  apply wp
                 apply (simp add: Collect_const_mem all_ex_eq_helper
                                  numeral_eqs syscall_error_rel_def
                                  exception_defs cintr_def intr_and_se_rel_def
                                  hd_drop_conv_nth2
                            cong: if_cong)
                 apply vcg
                apply (simp cong: if_cong)
                apply (wp hoare_drop_imps)
               apply (simp add: Collect_const_mem)
               apply (vcg exspec=slotCapLongRunningDelete_modifies)
              apply (simp cong: if_cong)
              apply (wp hoare_drop_imps)
             apply (simp add: Collect_const_mem all_ex_eq_helper
                              numeral_eqs syscall_error_rel_def
                              exception_defs cintr_def intr_and_se_rel_def)
             apply (vcg exspec=slotCapLongRunningDelete_modifies)
            apply (simp add: pred_conj_def cong: if_cong)
            apply (strengthen if_n_updateCapData_valid_strg)
            apply (wp hoare_drop_imps)
           apply (simp add: Collect_const_mem all_ex_eq_helper
                            numeral_eqs syscall_error_rel_def
                            exception_defs cintr_def intr_and_se_rel_def)
           apply vcg
          apply simp
          apply (wp hoare_drop_imps)
         apply (simp add: Collect_const_mem all_ex_eq_helper
                          numeral_eqs syscall_error_rel_def
                          exception_defs cintr_def intr_and_se_rel_def)
         apply vcg
        apply simp
        apply (wp hoare_drop_imps)
       apply (simp add: Collect_const_mem all_ex_eq_helper
                        numeral_eqs syscall_error_rel_def
                        exception_defs cintr_def intr_and_se_rel_def
                  cong: if_cong
                | vcg exspec=getSyscallArg_modifies
                | wp)+
  apply (clarsimp simp: word_less_nat_alt)
  apply (rule conjI)
   apply (clarsimp simp: ct_in_state'_def interpret_excaps_test_null
                         excaps_map_def neq_Nil_conv)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (rule conjI, clarsimp simp: sysargs_rel_n_def n_msgRegisters_def)
   apply (frule(2) tcb_at_capTCBPtr_CL)
   apply (auto simp: isCap_simps valid_tcb_state'_def objBits_defs mask_def
              elim!: pred_tcb'_weakenE
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: linorder_not_le interpret_excaps_test_null
                        excaps_map_def neq_Nil_conv word_sle_def
                        word_sless_def)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
  apply (clarsimp simp: mask_def[where n=4] ccap_rights_relation_def
                        rightsFromWord_wordFromRights
                        capTCBPtr_eq tcb_cnode_index_defs size_of_def
                        option_to_0_def rf_sr_ksCurThread
                        ThreadState_defs mask_eq_iff_w2p word_size)
  apply (simp add: word_sle_def cap_get_tag_isCap)
  apply (subgoal_tac "args \<noteq> []")
   apply (clarsimp simp: hd_conv_nth)
   apply (clarsimp simp: objBits_simps')
   apply fastforce
  apply clarsimp
  done

lemma invokeTCB_SetTLSBase_ccorres:
  notes hoare_weak_lift_imp [wp]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
   (invs')
   ({s. thread_' s = tcb_ptr_to_ctcb_ptr tcb}
         \<inter> {s. tls_base_' s = tls_base}) []
   (invokeTCB (SetTLSBase tcb tls_base))
   (Call invokeSetTLSBase_'proc)"
  apply (cinit lift: thread_' tls_base_')
   apply (simp add: liftE_def bind_assoc
               del: Collect_const)
   apply (ctac add: setRegister_ccorres)
     apply (rule ccorres_pre_getCurThread)
     apply (rename_tac cur_thr)
     apply (rule ccorres_split_nothrow_novcg_dc)
        apply (rule_tac R="\<lambda>s. cur_thr = ksCurThread s" in ccorres_when)
         apply (clarsimp simp: rf_sr_ksCurThread)
        apply clarsimp
        apply (ctac (no_vcg) add: rescheduleRequired_ccorres)
       apply (unfold return_returnOk)[1]
       apply (rule ccorres_return_CE, simp+)[1]
      apply (wpsimp wp: hoare_drop_imp simp: guard_is_UNIV_def)+
   apply vcg
  apply (clarsimp simp: tlsBaseRegister_def X64.tlsBaseRegister_def
                        invs_weak_sch_act_wf invs_queues TLS_BASE_def FS_BASE_def
                 split: if_split)
  done

lemma decodeSetTLSBase_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and sch_act_simple
              and (\<lambda>s. ksCurThread s = thread) and ct_active' and K (isThreadCap cp)
              and valid_cap' cp and (\<lambda>s. \<forall>x \<in> zobj_refs' cp. ex_nonz_cap_to' x s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeSetTLSBase args cp
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeSetTLSBase_'proc)"
  apply (cinit' lift: cap_' length___unsigned_long_' buffer_'
                simp: decodeSetTLSBase_def)
   apply wpc
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def
                          exception_defs syscall_error_rel_def
                          syscall_error_to_H_cases)
   apply (rule ccorres_cond_false_seq; simp)
   apply (rule ccorres_add_return,
          ctac add: getSyscallArg_ccorres_foo'[where args=args and n=0 and buffer=buffer])
     apply (simp add: invocationCatch_use_injection_handler
                      bindE_assoc injection_handler_returnOk
                      ccorres_invocationCatch_Inr performInvocation_def)
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply (ctac (no_vcg) add: invokeTCB_SetTLSBase_ccorres)
         apply simp
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply (wpsimp wp: sts_invs_minor')+
     apply (vcg exspec=setThreadState_modifies)
    apply wp
   apply vcg
  apply (clarsimp simp: Collect_const_mem)
  apply (rule conjI)
   apply (clarsimp simp: ct_in_state'_def sysargs_rel_n_def n_msgRegisters_def)
   apply (auto simp: valid_tcb_state'_def
              elim!: pred_tcb'_weakenE)[1]
  apply (simp add: ThreadState_defs mask_eq_iff_w2p word_size)
  apply (frule rf_sr_ksCurThread)
  apply (simp only: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply (auto simp: unat_eq_0 le_max_word_ucast_id)+
  done

lemma decodeTCBInvocation_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and valid_cap' cp and cte_at' slot and K (isThreadCap cp)
              and (excaps_in_mem extraCaps o ctes_of)
              and tcb_at' (capTCBPtr cp) and ex_nonz_cap_to' (capTCBPtr cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. invLabel_' s = label}
            \<inter> {s. ccap_relation cp (cap_' s)}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. slot_' s = cte_Ptr slot}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. call_' s = from_bool isCall}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeTCBInvocation label args cp slot extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeTCB)
     (Call decodeTCBInvocation_'proc)"
  apply (cinit' lift: invLabel_' cap_' length___unsigned_long_' slot_' current_extra_caps_' call_' buffer_')
   apply (simp add: decodeTCBInvocation_def invocation_eq_use_types gen_invocation_type_eq
               del: Collect_const)
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeReadRegisters_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeWriteRegisters_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeCopyRegisters_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac add: setThreadState_ccorres)
      apply csymbr
      apply (simp add: performInvocation_def)
      apply (ctac add: invokeTCB_Suspend_ccorres)
         apply simp
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply wp
      apply (vcg exspec=invokeTCB_Suspend_modifies)
     apply (wp sts_invs_minor')
    apply (vcg exspec=setThreadState_modifies)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac add: setThreadState_ccorres)
      apply csymbr
      apply (simp add: performInvocation_def)
      apply (ctac add: invokeTCB_Resume_ccorres)
         apply simp
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply wp
      apply (vcg exspec=invokeTCB_Resume_modifies)
     apply (wp sts_invs_minor')
    apply (vcg exspec=setThreadState_modifies)
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeTCBConfigure_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetPriority_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetMCPriority_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetSchedParams_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetIPCBuffer_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetSpace_ccorres [where buffer=buffer])
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeBindNotification_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeUnbindNotification_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_Cond_rhs)
    apply (simp add: gen_invocation_type_eq)
    apply (rule ccorres_add_returnOk, ctac(no_vcg) add: decodeSetTLSBase_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (rule ccorres_equals_throwError)
    apply (fastforce simp: throwError_bind invocationCatch_def
                   split: invocation_label.split gen_invocation_labels.split)
   apply (simp add: ccorres_cond_iffs
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule syscall_error_throwError_ccorres_n)
   apply (simp add: syscall_error_to_H_cases)
  apply (clarsimp simp: cintr_def intr_and_se_rel_def
                        exception_defs rf_sr_ksCurThread
                        Collect_const_mem)
  apply (rule conjI)
   apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def
              elim!: pred_tcb'_weakenE
              dest!: st_tcb_at_idle_thread')[1]
  apply (simp split: sum.split add: cintr_def intr_and_se_rel_def
                        exception_defs syscall_error_rel_def)
  apply (simp add: ThreadState_defs mask_eq_iff_w2p word_size)
  apply (simp add: cap_get_tag_isCap[symmetric], drule(1) cap_get_tag_to_H)
  apply clarsimp
  done

end
end
