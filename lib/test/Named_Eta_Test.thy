(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Named_Eta_Test
imports Lib.Named_Eta
begin

experiment
begin

declare [[eta_contract=false]] (* for display only, it does not affect terms *)

(* tactical invocation example *)
schematic_goal
  "\<And>y. ?Q y False \<Longrightarrow> ?P y (\<lambda>x. f x)"
  apply (tactic \<open>named_eta_tac "x" @{context}\<close>)
  apply assumption
  done

(* method invocation example *)
schematic_goal
  "\<And>y. ?Q y False \<Longrightarrow> ?P y (\<lambda>x. f x)"
  apply (named_eta x)
  apply assumption
  done

lemma
  "P x (\<lambda>z. g (\<lambda>x. f x) z)"
  "\<And>P z. Q z \<Longrightarrow> P (\<lambda>x. f x)"
  apply -
  (* only affects one subgoal *)
  prefer 2
  apply (named_eta x)
  prefer 2
  (* only contract "z" *)
  apply (named_eta z)
  (* now only contract "x" *)
  apply (named_eta x)
  oops

lemma (* nested lambdas *)
  "\<lbrakk> X; P (\<lambda>x. (f (\<lambda>x. g y x))) \<rbrakk> \<Longrightarrow> P (\<lambda>x. (f (\<lambda>x. g y x)))"
  apply (named_eta x)
  apply assumption
  done

ML \<open>
  (* nameless abstractions: *)
  val t = Abs ("", @{typ bool}, @{term "f (\<lambda>x. g x) :: bool \<Rightarrow> bool"} $ Bound 0)
  val ct = Thm.cterm_of @{context} t
  (* contracts only the nameless "a" lambda: *)
  val thm = Named_Eta.named_eta_conv "" @{context} ct
\<close>

end

end
