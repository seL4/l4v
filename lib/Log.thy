(*
 * Copyright 2021, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Discrete logarithm on nat and ceiling of discrete log. *)

theory Log
imports Main
begin

(* ceil_log : log 2 ceiling function for nat, which is used for SC size encoding *)

(* ceil_log is meant to be defined in terms of Discrete.log. In the below, however, we are using
   discrete_log, which is just a copy of Discrete.log. This is to avoid the breakage in rec_del
   (in ASpec) caused by importing Complex_Main via HOL-Library.Discrete.

   Below, a few lemmas for the properties we need about Discrete.log are copied from
   HOL-Library.Discrete along with the Discrete.log definition as discrete_log.

   FIXME: figure out why rec_del breaks with Complex_Main, and use HOL-Library.Discrete directly *)

(* Discrte.log and related lemmas, copied and renamed *)
fun discrete_log :: "nat \<Rightarrow> nat" where
  "discrete_log n = (if n < 2 then 0 else Suc (discrete_log (n div 2)))"

declare discrete_log.simps[simp del]

lemma discrete_log_zero [simp]: "discrete_log 0 = 0"
  by (simp add: discrete_log.simps)

lemma discrete_log_one [simp]: "discrete_log 1 = 0"
  by (simp add: discrete_log.simps)

lemma discrete_log_Suc_zero [simp]: "discrete_log (Suc 0) = 0"
  using discrete_log_one by simp

lemma discrete_log_rec: "n \<ge> 2 \<Longrightarrow> discrete_log n = Suc (discrete_log (n div 2))"
  by (simp add: discrete_log.simps)

lemma discrete_log_twice [simp]: "n \<noteq> 0 \<Longrightarrow> discrete_log (2 * n) = Suc (discrete_log n)"
  by (simp add: discrete_log_rec)

lemma discrete_log_half [simp]: "discrete_log (n div 2) = discrete_log n - 1"
proof (cases "n < 2")
  case True
  then have "n = 0 \<or> n = 1" by arith
  then show ?thesis by (auto simp del: One_nat_def)
next
  case False
  then show ?thesis by (simp add: discrete_log_rec)
qed

lemma discrete_log_exp [simp]: "discrete_log (2 ^ n) = n"
  by (induct n) simp_all

lemma discrete_log_mono: "mono discrete_log"
proof
  fix m n :: nat
  assume "m \<le> n"
  then show "discrete_log m \<le> discrete_log n"
  proof (induct m arbitrary: n rule: discrete_log.induct)
    case (1 m)
    then have mn2: "m div 2 \<le> n div 2" by arith
    show "discrete_log m \<le> discrete_log n"
    proof (cases "m \<ge> 2")
      case False
      then have "m = 0 \<or> m = 1" by arith
      then show ?thesis by (auto simp del: One_nat_def)
    next
      case True then have "\<not> m < 2" by simp
      with mn2 have "n \<ge> 2" by arith
      from True have m2_0: "m div 2 \<noteq> 0" by arith
      with mn2 have n2_0: "n div 2 \<noteq> 0" by arith
      from \<open>\<not> m < 2\<close> "1.hyps" mn2 have "discrete_log (m div 2) \<le> discrete_log (n div 2)" by blast
      with m2_0 n2_0 have "discrete_log (2 * (m div 2)) \<le> discrete_log (2 * (n div 2))" by simp
      with m2_0 n2_0 \<open>m \<ge> 2\<close> \<open>n \<ge> 2\<close> show ?thesis by (simp only: discrete_log_rec [of m] discrete_log_rec [of n]) simp
    qed
  qed
qed

lemma discrete_log_le_iff: "m \<le> n \<Longrightarrow> discrete_log m \<le> discrete_log n"
  by (rule monoD [OF discrete_log_mono])

lemma discrete_log_induct [consumes 1, case_names one double]:
  fixes n :: nat
  assumes "n > 0"
  assumes one: "P 1"
  assumes double: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
using \<open>n > 0\<close> proof (induct n rule: discrete_log.induct)
  fix n
  assume "\<not> n < 2 \<Longrightarrow>
          0 < n div 2 \<Longrightarrow> P (n div 2)"
  then have *: "n \<ge> 2 \<Longrightarrow> P (n div 2)" by simp
  assume "n > 0"
  show "P n"
  proof (cases "n = 1")
    case True
    with one show ?thesis by simp
  next
    case False
    with \<open>n > 0\<close> have "n \<ge> 2" by auto
    with * have "P (n div 2)" .
    with \<open>n \<ge> 2\<close> show ?thesis by (rule double)
  qed
qed

lemma discrete_log_exp2_le:
  assumes "n > 0"
  shows "2 ^ discrete_log n \<le> n"
  using assms
proof (induct n rule: discrete_log_induct)
  case one
  then show ?case by simp
next
  case (double n)
  with discrete_log_mono have "discrete_log n \<ge> Suc 0"
    by (simp add: discrete_log.simps)
  assume "2 ^ discrete_log (n div 2) \<le> n div 2"
  with \<open>n \<ge> 2\<close> have "2 ^ (discrete_log n - Suc 0) \<le> n div 2" by simp
  then have "2 ^ (discrete_log n - Suc 0) * 2 ^ 1 \<le> n div 2 * 2" by simp
  with \<open>discrete_log n \<ge> Suc 0\<close> have "2 ^ discrete_log n \<le> n div 2 * 2"
    unfolding power_add [symmetric] by simp
  also have "n div 2 * 2 \<le> n" by (cases "even n") simp_all
  finally show ?case .
qed

lemma discrete_log_exp2_gt: "2 * 2 ^ discrete_log n > n"
proof (cases "n > 0")
  case True
  thus ?thesis
  proof (induct n rule: discrete_log_induct)
    case (double n)
    thus ?case
      by (cases "even n") (auto elim!: evenE oddE simp: field_simps discrete_log.simps)
  qed simp_all
qed simp_all

lemma discrete_log_eqI:
  assumes "n > 0" "2^k \<le> n" "n < 2 * 2^k"
  shows   "discrete_log n = k"
proof (rule antisym)
  from \<open>n > 0\<close> have "2 ^ discrete_log n \<le> n" by (rule discrete_log_exp2_le)
  also have "\<dots> < 2 ^ Suc k" using assms by simp
  finally have "discrete_log n < Suc k" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "discrete_log n \<le> k" by simp
next
  have "2^k \<le> n" by fact
  also have "\<dots> < 2^(Suc (discrete_log n))" by (simp add: discrete_log_exp2_gt)
  finally have "k < Suc (discrete_log n)" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "k \<le> discrete_log n" by simp
qed

(* ceil_log *)
definition "ceil_log n \<equiv> if n = 0 then 0 else Suc (discrete_log (n - 1))"

lemma ceil_log_zero[simp]: "ceil_log 0 = 0" by (simp add: ceil_log_def)

lemma ceil_log_one[simp]: "ceil_log 1 = 1" by (simp add: ceil_log_def)

lemma ceil_log_Suc_zero[simp]: "ceil_log (Suc 0) = 1" by (simp add: ceil_log_def)

lemma ceil_log_le_mono:
  "x \<le> y \<Longrightarrow> ceil_log x \<le> ceil_log y"
  unfolding ceil_log_def
  by (clarsimp simp: discrete_log_le_iff)

lemma ceil_log_exp[simp]:
  "n > 0 \<Longrightarrow> ceil_log (2 ^n) = n"
  apply (simp add: ceil_log_def)
  apply (cases n; simp)
  apply (rule discrete_log_eqI)
    apply auto[1]
  using less_Suc_eq by fastforce+

lemma ceil_log_le_bound:
  "0 < n \<Longrightarrow> 2^(n-1) < x \<Longrightarrow> x \<le> 2^n \<Longrightarrow> n - 1 < ceil_log x"
  apply (simp add: ceil_log_def less_Suc_eq_le)
  apply (subgoal_tac "\<And>x y. x < y \<Longrightarrow> x \<le> y - Suc 0")
   apply (metis discrete_log_le_iff discrete_log_exp)
  apply arith
  done

end
