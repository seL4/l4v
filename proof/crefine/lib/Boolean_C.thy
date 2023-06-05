(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Definitions and rules for C boolean constants parsed from the kernel *)

theory Boolean_C
imports
  "CSpec.KernelInc_C"
begin

lemma true_and_1[simp]:
  "true && 1 = true"
  "signed true && 1 = signed true"
  "unsigned true && 1 = unsigned true"
  by (simp add: true_def)+

lemma to_bool_true[simp]:
  "to_bool true"
  "to_bool (signed true)"
  "to_bool (unsigned true)"
  by (simp add: to_bool_def true_def)+

lemma true_equals_simps[simp]:
  "true = 1 \<longleftrightarrow> True"
  "signed true = 1 \<longleftrightarrow> True"
  "unsigned true = 1 \<longleftrightarrow> True"
  "true = 0 \<longleftrightarrow> False"
  "signed true = 0 \<longleftrightarrow> False"
  "unsigned true = 0 \<longleftrightarrow> False"
  by (simp add: true_def)+

lemma true_eq_from_bool[simp]:
  "(true = from_bool P) = P"
  "(signed true = from_bool P) = P"
  "(unsigned true = from_bool P) = P"
  by (simp add: from_bool_def split: bool.splits)+

lemma false_and_1[simp]:
  "false && 1 = false"
  "signed false && 1 = signed false"
  "unsigned false && 1 = unsigned false"
  by (simp add: false_def)+

lemma to_bool_false[simp]:
  "\<not> to_bool false"
  "\<not> to_bool (signed false)"
  "\<not> to_bool (unsigned false)"
  by (simp add: to_bool_def false_def)+

lemma false_equals_simps[simp]:
  "false = 0 \<longleftrightarrow> True"
  "signed false = 0 \<longleftrightarrow> True"
  "unsigned false = 0 \<longleftrightarrow> True"
  "false = 1 \<longleftrightarrow> False"
  "signed false = 1 \<longleftrightarrow> False"
  "unsigned false = 1 \<longleftrightarrow> False"
  by (simp add: false_def)+

lemma false_eq_from_bool[simp]:
  "(false = from_bool P) = (\<not> P)"
  "(signed false = from_bool P) = (\<not> P)"
  "(unsigned false = from_bool P) = (\<not> P)"
  by (simp add: from_bool_def split: bool.splits)+

lemma from_bool_vals[simp]:
  "from_bool True = signed true"
  "from_bool False = signed false"
  by (simp add: from_bool_def)+

lemma true_neq_false[simp]:
  "true \<noteq> false"
  "signed true \<noteq> signed false"
  "unsigned true \<noteq> unsigned false"
  by (simp add: true_def false_def)+

(* The bitfield generator masks everything with the expected bit length, so we do that here too. *)
definition
  to_bool_bf :: "'a::len word \<Rightarrow> bool" where
  "to_bool_bf w \<equiv> (w && mask 1) = 1"

lemma to_bool_bf_mask1[simp]:
  "to_bool_bf (mask (Suc 0))"
  by (simp add: mask_def to_bool_bf_def)

lemma to_bool_bf_0[simp]:
  "\<not>to_bool_bf 0"
  by (simp add: to_bool_bf_def)

lemma to_bool_bf_1[simp]:
  "to_bool_bf 1"
  by (simp add: to_bool_bf_def mask_def)

lemma to_bool_bf_false[simp]:
  "\<not>to_bool_bf false"
  by (simp add: false_def)

lemma to_bool_bf_true[simp]:
  "to_bool_bf true"
  by (simp add: true_def)

lemma to_bool_to_bool_bf:
  "w = false \<or> w = true \<Longrightarrow> to_bool_bf w = to_bool w"
  by (auto simp: false_def true_def to_bool_def to_bool_bf_def mask_def)

lemma to_bool_bf_mask_1[simp]:
  "to_bool_bf (w && mask (Suc 0)) = to_bool_bf w"
  by (simp add: to_bool_bf_def)

lemma to_bool_bf_and[simp]:
  "to_bool_bf (a && b) = (to_bool_bf a \<and> to_bool_bf b)"
  apply (clarsimp simp: to_bool_bf_def)
  apply (rule iffI)
   apply (subst (asm) bang_eq)
   apply (simp add: word_size)
   apply (rule conjI)
    apply (rule word_eqI)
    apply (auto simp add: word_size)[1]
   apply (rule word_eqI)
   apply (auto simp add: word_size)[1]
  apply clarsimp
  apply (rule word_eqI)
  apply (subst (asm) bang_eq)+
  apply (auto simp add: word_size)[1]
  done

lemma to_bool_bf_to_bool_mask:
  "w && mask (Suc 0) = w \<Longrightarrow> to_bool_bf w = to_bool (w::machine_word)"
  by (metis mask_Suc_0 bool_mask mask_1 to_bool_0 to_bool_1 to_bool_bf_def word_gt_0)

lemma to_bool_mask_to_bool_bf:
  "to_bool (x && 1) = to_bool_bf (x::machine_word)"
  by (simp add: to_bool_bf_def to_bool_def)

end