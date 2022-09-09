(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Tactics/methods related to instantiating variables in multiple thms - Examples *)

theory Rules_Tac_Test
imports Lib.Rules_Tac
begin

experiment begin

lemmas thms = bexI exI

(* instantiating a variable in multiple thms *)

lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (rules_tac x=n in thms) (* combined thms *)
  apply assumption
  done

lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (rules_tac x=n in bexI exI) (* thms listed separately *)
  apply assumption
  done

lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (rules_tac x=n and P=k for z k in thms) (* irrelevant "for" fixes *)
  apply assumption
  done

lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (rules_tac x="P n" for P in exI) (* used for fixes *)
  oops

(* single-variable instantiation using single_instantiate_tac *)
lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (tactic \<open>
    let
      val v = Token.explode (Thy_Header.get_keywords' @{context}) Position.none "n"
              |> Parse.embedded_inner_syntax |> #1
    in
      Multi_Rule_Insts.single_instantiate_tac Rule_Insts.res_inst_tac "x" v [] @{thms thms}
      @{context} []
    end\<close>)
  apply assumption
  done

(* single-variable instantiation using single_instantiate_tac via a method *)

method_setup inst_x_exI_tac =
  \<open>Multi_Rule_Insts.single_instantiate_method Rule_Insts.res_inst_tac "x" @{thms thms}\<close>
  \<open>instantiate "x" in thms and apply the result with rule_tac\<close>

lemma "P n \<Longrightarrow> \<exists>x. P x"
  apply (inst_x_exI_tac n)
  apply assumption
  done

(* instantiation of same variable with a different type in each theorem *)
lemma
  assumes a: "\<And>x P. Z x \<Longrightarrow> P (x::nat)"
  assumes b: "\<And>x P. Y x \<Longrightarrow> P (x::int)"
  shows "P (2::nat)"
  apply (rules_tac x=2 in b a)
  oops

end

end
