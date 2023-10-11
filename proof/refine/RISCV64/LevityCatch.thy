(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory LevityCatch
imports
  "BaseRefine.Include"
  "Lib.LemmaBucket"
  "Lib.Corres_Method"
begin

(* Try again, clagged from Include *)
no_notation bind_drop (infixl ">>" 60)

lemma read_magnitudeCheck_assert:
  "read_magnitudeCheck x y n = oassert (case y of None \<Rightarrow> True | Some z \<Rightarrow> 1 << n \<le> z - x)"
  by (fastforce simp: read_magnitudeCheck_def split: option.split)

lemma magnitudeCheck_assert:
  "magnitudeCheck x y n = assert (case y of None \<Rightarrow> True | Some z \<Rightarrow> 1 << n \<le> z - x)"
  by (simp add: magnitudeCheck_def read_magnitudeCheck_assert)

context begin interpretation Arch . (*FIXME: arch_split*)
lemmas makeObject_simps =
  makeObject_endpoint makeObject_notification makeObject_cte
  makeObject_tcb makeObject_user_data makeObject_pte
  makeObject_asidpool
end

lemma projectKO_inv : "\<lbrace>P\<rbrace> gets_the $ projectKO ko \<lbrace>\<lambda>rv. P\<rbrace>"
  by wpsimp

(****** From GeneralLib *******)

lemma read_alignCheck_assert:
  "read_alignCheck ptr n = oassert (is_aligned ptr n)"
  by (simp add: is_aligned_mask read_alignCheck_def read_alignError_def ounless_def)

lemma alignCheck_assert:
  "alignCheck ptr n = assert (is_aligned ptr n)"
  by (simp add: read_alignCheck_assert alignCheck_def)

lemma magnitudeCheck_inv:   "\<lbrace>P\<rbrace> magnitudeCheck x y n \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (clarsimp simp add: magnitudeCheck_def split: option.splits)
  apply (wp when_wp)
  apply simp
  done

lemma alignCheck_inv:
  "\<lbrace>P\<rbrace> alignCheck x n \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: alignCheck_def unless_def alignError_def)
  apply (wp when_wp)
  apply simp
  done

lemma updateObject_default_inv:
  "\<lbrace>P\<rbrace> updateObject_default obj ko x y n \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding updateObject_default_def
  by (simp, wp magnitudeCheck_inv alignCheck_inv projectKO_inv, simp)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma to_from_apiType [simp]: "toAPIType (fromAPIType x) = Some x"
  by (cases x) (auto simp add: fromAPIType_def RISCV64_H.fromAPIType_def
                               toAPIType_def RISCV64_H.toAPIType_def)

end

end