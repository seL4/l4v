(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SubMonad_R
imports KHeap_R EmptyFail
begin

(* SubMonadLib *)
lemma submonad_doMachineOp:
  "submonad ksMachineState (ksMachineState_update \<circ> K) \<top> doMachineOp"
  apply (unfold_locales)
       apply (clarsimp simp: ext stateAssert_def doMachineOp_def o_def gets_def
                             get_def bind_def return_def submonad_fn_def)+
  done

interpretation submonad_doMachineOp:
  submonad ksMachineState "(ksMachineState_update \<circ> K)" \<top> doMachineOp
  by (rule submonad_doMachineOp)

lemma corres_machine_op':
  assumes P: "corres_underlying Id False True r P P' x x'"
  shows      "corres r (P \<circ> machine_state) (P' \<circ> ksMachineState) (do_machine_op x) (doMachineOp x')"
  apply (rule corres_submonad3 [OF submonad_do_machine_op submonad_doMachineOp _ _ _ _ P])
   apply (simp_all add: state_relation_def swp_def)
  done

lemma corres_machine_op:
  assumes P: "corres_underlying Id False True r \<top> \<top> x x'"
  shows      "corres r \<top> \<top> (do_machine_op x) (doMachineOp x')"
  by (rule corres_machine_op'[OF P, simplified])

lemmas corres_machine_op_Id = corres_machine_op[OF corres_Id]
lemmas corres_machine_op_Id_dc[corres_term] = corres_machine_op_Id[where r="dc::unit \<Rightarrow> unit \<Rightarrow> bool"]
lemmas corres_machine_op_Id_eq[corres_term] = corres_machine_op_Id[where r="(=)"]

lemmas corresK_machine_op =
  corres_machine_op[atomized, THEN corresK_lift_rule, rule_format, corresK]

lemma doMachineOp_mapM:
  assumes "\<And>x. empty_fail (m x)"
  shows "doMachineOp (mapM m l) = mapM (doMachineOp \<circ> m) l"
  apply (rule submonad_mapM [OF submonad_doMachineOp submonad_doMachineOp,
                                simplified])
  apply (rule assms)
  done

lemma doMachineOp_mapM_x:
  assumes "\<And>x. empty_fail (m x)"
  shows "doMachineOp (mapM_x m l) = mapM_x (doMachineOp \<circ> m) l"
  apply (rule submonad_mapM_x [OF submonad_doMachineOp submonad_doMachineOp,
                                simplified])
  apply (rule assms)
  done


context begin interpretation Arch . (*FIXME: arch-split*)
definition
  "asUser_fetch \<equiv> \<lambda>t s. case (ksPSpace s t) of
      Some (KOTCB tcb) \<Rightarrow> (atcbContextGet o tcbArch) tcb
    | None \<Rightarrow> undefined"

definition
  "asUser_replace \<equiv> \<lambda>t uc s.
      let obj = case (ksPSpace s t) of
                   Some (KOTCB tcb) \<Rightarrow> Some (KOTCB (tcb \<lparr>tcbArch := atcbContextSet uc (tcbArch tcb)\<rparr>))
                 | obj \<Rightarrow> obj
      in s \<lparr> ksPSpace := (ksPSpace s) (t := obj) \<rparr>"


lemma threadGet_stateAssert_gets_asUser:
  "threadGet (atcbContextGet o tcbArch) t = do stateAssert (tcb_at' t) []; gets (asUser_fetch t) od"
  apply (rule is_stateAssert_gets [OF _ _ empty_fail_threadGet no_fail_threadGet])
    apply (clarsimp simp: threadGet_def liftM_def, wp)
   apply (simp add: threadGet_def liftM_def, wp getObject_tcb_at')
  apply (simp add: threadGet_def liftM_def, wp)
   apply (rule hoare_strengthen_post, rule getObject_obj_at')
     apply (simp add: objBits_simps')+
   apply (clarsimp simp: obj_at'_def asUser_fetch_def projectKOs atcbContextGet_def)+
  done

lemma threadSet_modify_asUser:
  "tcb_at' t st \<Longrightarrow>
   threadSet (\<lambda>tcb. tcb\<lparr> tcbArch := atcbContextSet uc (tcbArch tcb)\<rparr>) t st = modify (asUser_replace t uc) st"
  apply (rule is_modify [OF _ empty_fail_threadSet no_fail_threadSet])
   apply (clarsimp simp: threadSet_def setObject_def split_def
                         updateObject_default_def)
   apply wp
   apply (rule_tac Q'="\<lambda>rv. obj_at' ((=) rv) t and ((=) st)" in hoare_post_imp)
    apply (clarsimp simp: asUser_replace_def Let_def obj_at'_def
                          projectKOs fun_upd_def
                   split: option.split kernel_object.split)
   apply (wp getObject_obj_at' | clarsimp simp: objBits_simps' atcbContextSet_def)+
  done

lemma atcbContext_get_eq[simp] : "atcbContextGet (atcbContextSet x atcb) = x"
  by(simp add: atcbContextGet_def atcbContextSet_def)

lemma atcbContext_set_eq[simp] : "atcbContextSet (atcbContextGet t) t = t"
  by (cases t, simp add: atcbContextGet_def atcbContextSet_def)


lemma atcbContext_set_set[simp] : "atcbContextSet x (atcbContextSet y atcb) = atcbContextSet x atcb"
  by (cases atcb ,simp add: atcbContextSet_def)

lemma submonad_asUser:
  "submonad (asUser_fetch t) (asUser_replace t) (tcb_at' t) (asUser t)"
  apply (unfold_locales)
      apply (clarsimp simp: asUser_fetch_def asUser_replace_def
                            Let_def obj_at'_def projectKOs
                     split: kernel_object.split option.split)
     apply (clarsimp simp: asUser_replace_def Let_def
                    split: kernel_object.split option.split)
     apply (rename_tac tcb)
     apply (case_tac tcb, simp)
    apply (clarsimp simp: asUser_fetch_def asUser_replace_def Let_def
                          fun_upd_idem
                   split: kernel_object.splits option.splits)
    apply (rename_tac tcb)
    apply (case_tac tcb, simp add: map_upd_triv atcbContextSet_def)
   apply (clarsimp simp: obj_at'_def asUser_replace_def
                         Let_def projectKOs atcbContextSet_def
                  split: kernel_object.splits option.splits)
   apply (rename_tac tcb)
   apply (case_tac tcb, simp add: objBitsKO_def ps_clear_def)
  apply (rule ext)
  apply (clarsimp simp: submonad_fn_def asUser_def bind_assoc split_def)
  apply (subst threadGet_stateAssert_gets_asUser, simp add: bind_assoc, rule ext)
  apply (rule bind_apply_cong [OF refl])+
  apply (rule bind_apply_cong [OF threadSet_modify_asUser])
   apply (clarsimp simp: in_monad stateAssert_def select_f_def)
  apply (rule refl)
  done

end

global_interpretation submonad_asUser:
  submonad "asUser_fetch t" "asUser_replace t" "tcb_at' t" "asUser t"
  by (rule submonad_asUser)

lemma doMachineOp_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> doMachineOp m \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_f_wp)
  apply simp
  done

end
