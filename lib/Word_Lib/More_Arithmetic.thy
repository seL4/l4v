(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Arithmetic lemmas\<close>

theory More_Arithmetic
  imports Main "HOL-Library.Type_Length"
begin

lemma n_less_equal_power_2:
  "n < 2 ^ n"
  by (fact less_exp)

lemma min_pm [simp]: "min a b + (a - b) = a"
  for a b :: nat
  by arith

lemma min_pm1 [simp]: "a - b + min a b = a"
  for a b :: nat
  by arith

lemma rev_min_pm [simp]: "min b a + (a - b) = a"
  for a b :: nat
  by arith

lemma rev_min_pm1 [simp]: "a - b + min b a = a"
  for a b :: nat
  by arith

lemma min_minus [simp]: "min m (m - k) = m - k"
  for m k :: nat
  by arith

lemma min_minus' [simp]: "min (m - k) m = m - k"
  for m k :: nat
  by arith

lemma nat_less_power_trans:
  fixes n :: nat
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  shows "2 ^ k * n < 2 ^ m"
proof (rule order_less_le_trans)
  show "2 ^ k * n < 2 ^ k * 2 ^ (m - k)"
    by (rule mult_less_mono2 [OF nv zero_less_power]) simp
  show "(2::nat) ^ k * 2 ^ (m - k) \<le> 2 ^ m" using nv kv
    by (subst power_add [symmetric]) simp
qed

lemma nat_le_power_trans:
  fixes n :: nat
  shows "\<lbrakk>n \<le> 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> 2 ^ k * n \<le> 2 ^ m"
  by (simp add: less_eq_div_iff_mult_less_eq mult.commute power_diff)

lemma nat_add_offset_less:
  fixes x :: nat
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n" and "0 < qy"
    by (auto dest: less_imp_add_positive)

  have "x * 2 ^ n + y < x * 2 ^ n + 2 ^ n" by simp fact+
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y < 2 ^ (m + n)" .
qed

lemma nat_power_less_diff:
  assumes lt: "(2::nat) ^ n * q < 2 ^ m"
  shows "q < 2 ^ (m - n)"
  using lt
proof (induct n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  by (cases m) auto
qed

lemma power_2_mult_step_le:
  assumes "n' \<le> n" and less: "2^n' * k' < 2^n * k"
  shows "2 ^ n' * (k' + 1) \<le> 2 ^ n * (k::nat)"
proof (cases "n'=n")
  case True
  then show ?thesis
    by (metis Suc_eq_plus1 Suc_leI less mult.commute mult_le_mono1 mult_less_cancel2)
next
  case False
  with assms have "n' < n"
    by simp
  then obtain m where "n = n' + m"
    using assms less_eqE by blast
  moreover have "k'+1 \<le> 2 ^ m * k"
    by (smt (verit, ccfv_threshold) Suc_eq_plus1 Suc_leI calculation less linorder_not_le mult.assoc mult.commute mult_le_mono1 power_add)
  ultimately show ?thesis
    by (metis mult.assoc mult_le_mono2 power_add)
qed

lemma nat_mult_power_less_eq:
  "b > 0 \<Longrightarrow> (a * b ^ n < (b :: nat) ^ m) = (a < b ^ (m - n))"
  using mult_less_cancel2[where m = a and k = "b ^ n" and n="b ^ (m - n)"]
        mult_less_cancel2[where m="a * b ^ (n - m)" and k="b ^ m" and n=1]
  by (smt (verit,del_insts) diff_is_0_eq leI le_add_diff_inverse2 less_one
      mult.assoc mult_eq_0_iff not_less_iff_gr_or_eq power_0 power_add zero_less_power)

lemma diff_diff_less:
  "(i < m - (m - (n :: nat))) = (i < m \<and> i < n)"
  by auto

lemma small_powers_of_2:
  \<open>x < 2 ^ (x - 1)\<close> if \<open>x \<ge> 3\<close> for x :: nat
proof -
  define m where \<open>m = x - 3\<close>
  with that have \<open>x = m + 3\<close>
    by simp
  moreover have \<open>m + 3 < 4 * 2 ^ m\<close>
    by (induction m) simp_all
  ultimately show ?thesis
    by simp
qed

lemma msrevs:
  "0 < n \<Longrightarrow> (k * n + m) div n = m div n + k"
  "(k * n + m) mod n = m mod n"
  for n :: nat
  by simp_all

lemma eq_mod_iff: "0 < n \<Longrightarrow> b = b mod n \<longleftrightarrow> 0 \<le> b \<and> b < n"
  for b n :: int
  by (metis pos_mod_bound pos_mod_sign zmod_trivial_iff)

end
