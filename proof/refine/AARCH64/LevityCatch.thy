(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory LevityCatch
imports
  "BaseRefine.Include"
  "Lib.AddUpdSimps"
  "Lib.LemmaBucket"
  "Lib.SimpStrategy"
  "Lib.Corres_Method"
begin

no_notation bind_drop (infixl ">>" 60)

lemma magnitudeCheck_assert:
  "magnitudeCheck x y n = assert (case y of None \<Rightarrow> True | Some z \<Rightarrow> 1 << n \<le> z - x)"
  by (fastforce simp: magnitudeCheck_def assert_def when_def
                split: option.split)

lemma projectKO_inv: "projectKO ko \<lbrace>P\<rbrace>"
  by (simp add: projectKO_def fail_def valid_def return_def
           split: option.splits)

lemma alignCheck_assert:
  "alignCheck ptr n = assert (is_aligned ptr n)"
  by (simp add: is_aligned_mask alignCheck_def assert_def
                alignError_def unless_def when_def)

lemma magnitudeCheck_inv:
  "magnitudeCheck x y n \<lbrace>P\<rbrace>"
  by (wpsimp simp: magnitudeCheck_def)

lemma alignCheck_inv:
  "alignCheck x n \<lbrace>P\<rbrace>"
  by (wpsimp simp: alignCheck_def alignError_def)

lemma updateObject_default_inv:
  "updateObject_default obj ko ptr ptr' next \<lbrace>P\<rbrace>"
  unfolding updateObject_default_def
  by (wpsimp wp: magnitudeCheck_inv alignCheck_inv projectKO_inv)


context begin interpretation Arch .

lemmas makeObject_simps =
  makeObject_endpoint makeObject_notification makeObject_cte
  makeObject_tcb makeObject_user_data makeObject_pte makeObject_asidpool

lemma to_from_apiType[simp]: "toAPIType (fromAPIType x) = Some x"
  by (cases x) (auto simp: fromAPIType_def toAPIType_def)

end

end
