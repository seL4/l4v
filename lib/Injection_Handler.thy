(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Definition of injection_handler and supporting lemmas. *)

theory Injection_Handler
  imports Monads.Nondet_VCG
begin

definition injection_handler ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('s, 'a + 'c) nondet_monad \<Rightarrow> ('s, 'b + 'c) nondet_monad" where
  "injection_handler f m \<equiv> m <handle2> (\<lambda>ft. throwError (f ft))"

lemma injection_wp:
  "\<lbrakk> t = injection_handler f; \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>ft. E (f ft)\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> t m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding injection_handler_def
  by wpsimp

lemma injection_wp_E:
  "\<lbrakk> t = injection_handler f; \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> t m \<lbrace>Q\<rbrace>,-"
  by (simp add: validE_R_def injection_wp)

lemma injection_bindE:
  "\<lbrakk> t = injection_handler f; t2 = injection_handler f \<rbrakk>
    \<Longrightarrow> t (x >>=E y) = (t2 x) >>=E (\<lambda>rv. t (y rv))"
  apply (simp add: injection_handler_def bindE_def handleE'_def bind_assoc)
  apply (rule arg_cong [where f="bind x"])
  apply (fastforce simp: lift_def throwError_def split: sum.splits)
  done

lemma injection_liftE:
  "t = injection_handler f \<Longrightarrow> t (liftE x) = liftE x"
  by (simp add: injection_handler_def handleE'_def liftE_def)

lemma id_injection:
  "id = injection_handler id"
proof -
  have P: "case_sum throwError (\<lambda>v. return (Inr v)) = return"
    by (auto simp: throwError_def split: sum.splits)
  show ?thesis
    by (auto simp: injection_handler_def handleE'_def P)
qed

lemma injection_handler_assertE:
  "injection_handler inject (assertE f) = assertE f"
  by (simp add: assertE_liftE injection_liftE)

end