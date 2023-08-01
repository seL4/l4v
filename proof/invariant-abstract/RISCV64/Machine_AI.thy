(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Properties of machine operations.
*)

theory Machine_AI
imports Bits_AI
begin


definition
  "no_irq f \<equiv> \<forall>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"

lemma wpc_helper_no_irq:
  "no_irq f \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (no_irq f)"
  by (simp add: wpc_helper_def)

wpc_setup "\<lambda>m. no_irq m" wpc_helper_no_irq

ML \<open>
structure CrunchNoIrqInstance : CrunchInstance =
struct
  val name = "no_irq";
  val prefix_name_scheme = true;
  type extra = unit;
  val eq_extra = op =;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => error "no_irq does not need a precondition";
  val has_preconds = false;
  fun mk_term _ body _ =
    (Syntax.parse_term @{context} "no_irq") $ body;
  fun dest_term (Const (@{const_name no_irq}, _) $ body)
    = SOME (Term.dummy, body, ())
    | dest_term _ = NONE;
  fun put_precond _ _ = error "crunch no_irq should not be calling put_precond";
  val pre_thms = [];
  val wpc_tactic = wp_cases_tactic_weak;
  fun wps_tactic _ _ _ = no_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. no_irq mapp_lambda_ignore";
  val get_monad_state_type = get_nondet_monad_state_type;
end;

structure CrunchNoIrq : CRUNCH = Crunch(CrunchNoIrqInstance);
\<close>

setup \<open>
  add_crunch_instance "no_irq" (CrunchNoIrq.crunch_x, CrunchNoIrq.crunch_ignore_add_dels)
\<close>

crunch_ignore (no_irq) (add:
  Nondet_Monad.bind return "when" get gets fail
  assert put modify unless select
  alternative assert_opt gets_the
  returnOk throwError lift bindE
  liftE whenE unlessE throw_opt
  assertE liftM liftME sequence_x
  zipWithM_x mapM_x sequence mapM sequenceE_x
  mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x
  zipWithM ignore_failure)

context Arch begin

lemma det_getRegister: "det (getRegister x)"
  by (simp add: getRegister_def)

lemma det_setRegister: "det (setRegister x w)"
  by (simp add: setRegister_def det_def modify_def get_def put_def bind_def)


lemma det_getRestartPC: "det getRestartPC"
  by (simp add: getRestartPC_def det_getRegister)


lemma det_setNextPC: "det (setNextPC p)"
  by (simp add: setNextPC_def det_setRegister)

(* FIXME empty_fail: make all empty_fail [intro!, wp], and non-conditional ones [simp] *)
lemma ef_loadWord: "empty_fail (loadWord x)"
  by (fastforce simp: loadWord_def)


lemma ef_storeWord: "empty_fail (storeWord x y)"
  by (fastforce simp: storeWord_def)


lemma no_fail_getRestartPC: "no_fail \<top> getRestartPC"
  by (simp add: getRestartPC_def getRegister_def)


lemma no_fail_loadWord [wp]: "no_fail (\<lambda>_. is_aligned p 3) (loadWord p)"
  apply (simp add: loadWord_def is_aligned_mask [symmetric])
  apply (rule no_fail_pre)
   apply wp
  apply simp
  done


lemma no_fail_storeWord: "no_fail (\<lambda>_. is_aligned p 3) (storeWord p w)"
  apply (simp add: storeWord_def is_aligned_mask [symmetric])
  apply (rule no_fail_pre)
   apply (wp)
  apply simp
  done


lemma no_fail_machine_op_lift [simp]:
  "no_fail \<top> (machine_op_lift f)"
  by (simp add: machine_op_lift_def)


lemma ef_machine_op_lift [simp]:
  "empty_fail (machine_op_lift f)"
  by (simp add: machine_op_lift_def)



lemma no_fail_setNextPC: "no_fail \<top> (setNextPC pc)"
  by (simp add: setNextPC_def setRegister_def)


lemma no_fail_initL2Cache: "no_fail \<top> initL2Cache"
  by (simp add: initL2Cache_def)

lemma no_fail_resetTimer[wp]: "no_fail \<top> resetTimer"
  by (simp add: resetTimer_def)


lemma loadWord_inv: "\<lbrace>P\<rbrace> loadWord x \<lbrace>\<lambda>x. P\<rbrace>"
  apply (simp add: loadWord_def)
  apply wp
  apply simp
  done


lemma getRestartPC_inv: "\<lbrace>P\<rbrace> getRestartPC \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getRestartPC_def getRegister_def)



lemma no_fail_clearMemory[simp, wp]:
  "no_fail (\<lambda>_. is_aligned p 3) (clearMemory p b)"
  apply (simp add: clearMemory_def mapM_x_mapM)
  apply (rule no_fail_pre)
   apply (wp no_fail_mapM' no_fail_storeWord )
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
  apply simp
  done

lemma no_fail_freeMemory[simp, wp]:
  "no_fail (\<lambda>_. is_aligned p 3) (freeMemory p b)"
  apply (simp add: freeMemory_def mapM_x_mapM)
  apply (rule no_fail_pre)
  apply (wp no_fail_mapM' no_fail_storeWord)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
  apply simp
  done


lemma no_fail_getActiveIRQ[wp]:
  "no_fail \<top> (getActiveIRQ in_kernel)"
  apply (simp add: getActiveIRQ_def)
  apply (rule no_fail_pre)
   apply (wp no_fail_select)
  apply simp
  done

definition "irq_state_independent P \<equiv> \<forall>f s. P s \<longrightarrow> P (irq_state_update f s)"

lemma getActiveIRQ_inv [wp]:
  "\<lbrakk>irq_state_independent P\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply (simp add: irq_state_independent_def)
  done

lemma no_fail_ackInterrupt[wp]: "no_fail \<top> (ackInterrupt irq)"
  by (simp add: ackInterrupt_def)


lemma no_fail_maskInterrupt[wp]: "no_fail \<top> (maskInterrupt irq bool)"
  by (simp add: maskInterrupt_def)



lemma no_irq_use:
  "\<lbrakk> no_irq f; (rv,s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> irq_masks s' = irq_masks s"
  apply (simp add: no_irq_def valid_def)
  apply (erule_tac x="\<lambda>x. x = irq_masks s" in allE)
  apply fastforce
  done

lemma no_irq_machine_rest_lift:
  "no_irq (machine_rest_lift f)"
  apply (clarsimp simp: no_irq_def machine_rest_lift_def split_def)
  apply wp
  apply simp
  done

crunch (no_irq) no_irq[wp, simp]: machine_op_lift

lemma no_irq:
  "no_irq f \<Longrightarrow> \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  by (simp add: no_irq_def)

lemma no_irq_initL2Cache: "no_irq  initL2Cache"
  by (simp add: initL2Cache_def)

lemma no_irq_gets [simp]:
  "no_irq (gets f)"
  by (simp add: no_irq_def)


lemma no_irq_resetTimer: "no_irq resetTimer"
  by (simp add: resetTimer_def)


lemma no_irq_debugPrint: "no_irq (debugPrint $ xs)"
  by (simp add: no_irq_def)

context notes no_irq[wp] begin

lemma no_irq_ackInterrupt: "no_irq (ackInterrupt irq)"
  by (wp | clarsimp simp: no_irq_def ackInterrupt_def)+

lemma no_irq_setIRQTrigger: "no_irq (setIRQTrigger irq bool)"
  by (wp | clarsimp simp: no_irq_def setIRQTrigger_def)+

lemma no_irq_loadWord: "no_irq (loadWord x)"
  apply (clarsimp simp: no_irq_def)
  apply (rule loadWord_inv)
  done


lemma no_irq_getActiveIRQ: "no_irq (getActiveIRQ in_kernel)"
  apply (clarsimp simp: no_irq_def)
  apply (rule getActiveIRQ_inv)
  apply (simp add: irq_state_independent_def)
  done


lemma no_irq_mapM:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM f xs)"
  apply (subst no_irq_def)
  apply clarify
  apply (rule mapM_wp)
   prefer 2
   apply (rule order_refl)
  apply (wp; simp)
  done


lemma no_irq_mapM_x:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM_x f xs)"
  apply (subst no_irq_def)
  apply clarify
  apply (rule mapM_x_wp)
   prefer 2
   apply (rule order_refl)
  apply (wp; simp)
  done


lemma no_irq_swp:
  "no_irq (f y x) \<Longrightarrow> no_irq (swp f x y)"
  by (simp add: swp_def)


lemma no_irq_seq [wp]:
  "\<lbrakk> no_irq f; \<And>x. no_irq (g x) \<rbrakk> \<Longrightarrow> no_irq (f >>= g)"
  apply (subst no_irq_def)
  apply clarsimp
  apply (rule hoare_seq_ext)
  apply (wp|simp)+
  done

lemma no_irq_return [simp, wp]: "no_irq (return v)"
  unfolding no_irq_def return_def
  by (rule allI, simp add: valid_def)


lemma no_irq_fail [simp, wp]: "no_irq fail"
  unfolding no_irq_def fail_def
  by (rule allI, simp add: valid_def)



lemma no_irq_assert [simp, wp]: "no_irq (assert P)"
  unfolding assert_def by simp

lemma no_irq_modify:
  "(\<And>s. irq_masks (f s) = irq_masks s) \<Longrightarrow> no_irq (modify f)"
  unfolding modify_def no_irq_def
  apply (rule allI, simp add: valid_def put_def get_def)
  apply (clarsimp simp: in_monad)
  done

lemma no_irq_storeWord: "no_irq (storeWord w p)"
  apply (simp add: storeWord_def)
  apply (wp no_irq_modify)
  apply simp
  done

lemma no_irq_when:
  "\<lbrakk>P \<Longrightarrow> no_irq f\<rbrakk> \<Longrightarrow> no_irq (when P f)"
  by (simp add: when_def)

lemma no_irq_clearMemory: "no_irq (clearMemory a b)"
  apply (simp add: clearMemory_def)
  apply (wp no_irq_mapM_x no_irq_storeWord)
  done

lemma getActiveIRQ_le_maxIRQ':
  "\<lbrace>\<lambda>s. \<forall>irq > maxIRQ. irq_masks s irq\<rbrace>
    getActiveIRQ in_kernel
   \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: linorder_not_le)
  done

lemma getActiveIRQ_neq_non_kernel:
  "\<lbrace>\<top>\<rbrace> getActiveIRQ True \<lbrace>\<lambda>rv s. rv \<notin> Some ` non_kernel_IRQs \<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply auto
  done

lemma dmo_getActiveIRQ_non_kernel[wp]:
  "\<lbrace>\<top>\<rbrace> do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> irq \<in> non_kernel_IRQs \<longrightarrow> P irq s\<rbrace>"
  unfolding do_machine_op_def
  apply wpsimp
  apply (drule use_valid, rule getActiveIRQ_neq_non_kernel, rule TrueI)
  apply clarsimp
  done

lemma empty_fail_initL2Cache: "empty_fail initL2Cache"
  by (simp add: initL2Cache_def)

lemma empty_fail_clearMemory [simp, intro!]:
  "\<And>a b. empty_fail (clearMemory a b)"
  by (fastforce simp: clearMemory_def mapM_x_mapM ef_storeWord)

lemma no_irq_setVSpaceRoot:
  "no_irq (setVSpaceRoot r a)"
  unfolding setVSpaceRoot_def by wpsimp

lemma no_irq_hwASIDFlush:
  "no_irq (hwASIDFlush r)"
  unfolding hwASIDFlush_def by wpsimp

end
end

context begin interpretation Arch .

requalify_facts
  det_getRegister
  det_setRegister
  det_getRestartPC
  det_setNextPC

end

end
