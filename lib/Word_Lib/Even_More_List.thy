(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Lemmas on list operations\<close>

theory Even_More_List
  imports Main
begin

lemma upt_add_eq_append':
  assumes "i \<le> j" and "j \<le> k"
  shows "[i..<k] = [i..<j] @ [j..<k]"
  using assms le_Suc_ex upt_add_eq_append by blast

lemma map_idem_upt_eq:
  \<open>map f [m..<n] = [m..<n]\<close> if \<open>\<And>q. m \<le> q \<Longrightarrow> q < n \<Longrightarrow> f q = q\<close>
proof (cases \<open>n \<ge> m\<close>)
  case False
  then show ?thesis
    by simp
next
  case True
  moreover define r where \<open>r = n - m\<close>
  ultimately have \<open>n = m + r\<close>
    by simp
  with that have \<open>\<And>q. m \<le> q \<Longrightarrow> q < m + r \<Longrightarrow> f q = q\<close>
    by simp
  then have \<open>map f [m..<m + r] = [m..<m + r]\<close>
    by (induction r) simp_all
  with \<open>n = m + r\<close> show ?thesis
    by simp
qed

lemma upt_zero_numeral_unfold:
  \<open>[0..<numeral n] = [0..<pred_numeral n] @ [pred_numeral n]\<close>
  by (simp add: numeral_eq_Suc)

lemma length_takeWhile_less:
  "\<exists>x\<in>set xs. \<not> P x \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (induct xs) (auto split: if_splits)

lemma Min_eq_length_takeWhile:
  \<open>Min {m. P m} = length (takeWhile (Not \<circ> P) ([0..<n]))\<close>
  if *: \<open>\<And>m. P m \<Longrightarrow> m < n\<close> and \<open>\<exists>m. P m\<close>
proof -
  from \<open>\<exists>m. P m\<close> obtain r where \<open>P r\<close> ..
  have \<open>Min {m. P m} = q + length (takeWhile (Not \<circ> P) ([q..<n]))\<close>
    if \<open>q \<le> n\<close> \<open>\<And>m. P m \<Longrightarrow> q \<le> m \<and> m < n\<close> for q
  using that proof (induction rule: inc_induct)
    case base
    from base [of r] \<open>P r\<close> show ?case
      by simp
  next
    case (step q)
    from \<open>q < n\<close> have *: \<open>[q..<n] = q # [Suc q..<n]\<close>
      by (simp add: upt_rec)
    show ?case
    proof (cases \<open>P q\<close>)
      case False
      then have \<open>Suc q \<le> m \<and> m < n\<close> if \<open>P m\<close> for m
        using that step.prems [of m] by (auto simp add: Suc_le_eq less_le)
      with \<open>\<not> P q\<close> show ?thesis
        by (simp add: * step.IH)
    next
      case True
      have \<open>{a. P a} \<subseteq> {0..n}\<close>
        using step.prems by (auto simp add: less_imp_le_nat)
      moreover have \<open>finite {0..n}\<close>
        by simp
      ultimately have \<open>finite {a. P a}\<close>
        by (rule finite_subset)
      with \<open>P q\<close> step.prems show ?thesis
        by (auto intro: Min_eqI simp add: *)
    qed
  qed
  from this [of 0] and that show ?thesis
    by simp
qed

lemma Max_eq_length_takeWhile:
  \<open>Max {m. P m} = n - Suc (length (takeWhile (Not \<circ> P) (rev [0..<n])))\<close>
  if *: \<open>\<And>m. P m \<Longrightarrow> m < n\<close> and \<open>\<exists>m. P m\<close>
using * proof (induction n)
  case 0
  with \<open>\<exists>m. P m\<close> show ?case
    by auto
next
  case (Suc n)
  show ?case
  proof (cases \<open>P n\<close>)
    case False
    then have \<open>m < n\<close> if \<open>P m\<close> for m
      using that Suc.prems [of m] by (auto simp add: less_le)
    with Suc.IH show ?thesis
      by auto
  next
    case True
    have \<open>{a. P a} \<subseteq> {0..n}\<close>
      using Suc.prems by (auto simp add: less_Suc_eq_le)
    moreover have \<open>finite {0..n}\<close>
      by simp
    ultimately have \<open>finite {a. P a}\<close>
      by (rule finite_subset)
    with \<open>P n\<close> Suc.prems show ?thesis
      by (auto intro: Max_eqI simp add: less_Suc_eq_le)
  qed
qed

end
