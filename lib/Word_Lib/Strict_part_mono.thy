(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Strict_part_mono
  imports "HOL-Library.Word" More_Word
begin

definition
  strict_part_mono :: "'a set \<Rightarrow> ('a :: order \<Rightarrow> 'b :: order) \<Rightarrow> bool" where
 "strict_part_mono S f \<equiv> \<forall>A\<in>S. \<forall>B\<in>S. A < B \<longrightarrow> f A < f B"

lemma strict_part_mono_by_steps:
  "strict_part_mono {..n :: nat} f = (n \<noteq> 0 \<longrightarrow> f (n - 1) < f n \<and> strict_part_mono {.. n - 1} f)"
  apply (cases n; simp add: strict_part_mono_def)
  apply (safe; clarsimp)
  apply (case_tac "B = Suc nat"; simp)
  apply (case_tac "A = nat"; clarsimp)
  apply (erule order_less_trans [rotated])
  apply simp
  done

lemma strict_part_mono_singleton[simp]:
  "strict_part_mono {x} f"
  by (simp add: strict_part_mono_def)

lemma strict_part_mono_lt:
  "\<lbrakk> x < f 0; strict_part_mono {.. n :: nat} f \<rbrakk> \<Longrightarrow> \<forall>m \<le> n. x < f m"
  by (auto simp add: strict_part_mono_def Ball_def intro: order.strict_trans)

lemma strict_part_mono_reverseE:
  "\<lbrakk> f n \<le> f m; strict_part_mono {.. N :: nat} f; n \<le> N \<rbrakk> \<Longrightarrow> n \<le> m"
  by (rule ccontr) (fastforce simp: linorder_not_le strict_part_mono_def)

lemma two_power_strict_part_mono:
  "strict_part_mono {..LENGTH('a) - 1} (\<lambda>x. (2 :: 'a :: len word) ^ x)"
proof -
  { fix n
    have "n < LENGTH('a) \<Longrightarrow> strict_part_mono {..n} (\<lambda>x. (2 :: 'a :: len word) ^ x)"
    proof (induct n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      from Suc.prems
      have "2 ^ n < (2 :: 'a :: len word) ^ Suc n"
        using power_strict_increasing unat_power_lower word_less_nat_alt by fastforce
      with Suc
      show ?case by (subst strict_part_mono_by_steps) simp
    qed
  }
  then show ?thesis by simp
qed

end
