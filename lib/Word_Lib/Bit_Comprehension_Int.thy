(*
 * Copyright Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Comprehension syntax for \<open>int\<close>\<close>

theory Bit_Comprehension_Int
  imports
    Bit_Comprehension
begin

instantiation int :: bit_comprehension
begin

definition
  \<open>set_bits f = (
      if \<exists>n. \<forall>m\<ge>n. f m = f n then
      let n = LEAST n. \<forall>m\<ge>n. f m = f n
      in signed_take_bit n (horner_sum of_bool 2 (map f [0..<Suc n]))
     else 0 :: int)\<close>

instance proof
  fix k :: int
  from int_bit_bound [of k]
  obtain n where *: \<open>\<And>m. n \<le> m \<Longrightarrow> bit k m \<longleftrightarrow> bit k n\<close>
    and **: \<open>n > 0 \<Longrightarrow> bit k (n - 1) \<noteq> bit k n\<close>
    by blast
  then have ***: \<open>\<exists>n. \<forall>n'\<ge>n. bit k n' \<longleftrightarrow> bit k n\<close>
    by meson
  have l: \<open>(LEAST q. \<forall>m\<ge>q. bit k m \<longleftrightarrow> bit k q) = n\<close>
    apply (rule Least_equality)
    using * apply blast
    apply (metis "**" One_nat_def Suc_pred le_cases le0 neq0_conv not_less_eq_eq)
    done
  show \<open>set_bits (bit k) = k\<close>
    apply (simp only: *** set_bits_int_def horner_sum_bit_eq_take_bit l)
    apply simp
    apply (rule bit_eqI)
    apply (simp add: bit_signed_take_bit_iff min_def)
    apply (auto simp add: not_le bit_take_bit_iff dest: *)
    done
qed

end

lemma int_set_bits_K_False [simp]: "(BITS _. False) = (0 :: int)"
  by (simp add: set_bits_int_def)

lemma int_set_bits_K_True [simp]: "(BITS _. True) = (-1 :: int)"
  by (simp add: set_bits_int_def)

lemma set_bits_code [code]:
  "set_bits = Code.abort (STR ''set_bits is unsupported on type int'') (\<lambda>_. set_bits :: _ \<Rightarrow> int)"
  by simp

lemma set_bits_int_unfold':
  \<open>set_bits f =
    (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
      let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
      in horner_sum of_bool 2 (map f [0..<n])
     else if \<exists>n. \<forall>n'\<ge>n. f n' then
      let n = LEAST n. \<forall>n'\<ge>n. f n'
      in signed_take_bit n (horner_sum of_bool 2 (map f [0..<n] @ [True]))
     else 0 :: int)\<close>
proof (cases \<open>\<exists>n. \<forall>m\<ge>n. f m \<longleftrightarrow> f n\<close>)
  case True
  then obtain q where q: \<open>\<forall>m\<ge>q. f m \<longleftrightarrow> f q\<close>
    by blast
  define n where \<open>n = (LEAST n. \<forall>m\<ge>n. f m \<longleftrightarrow> f n)\<close>
  have \<open>\<forall>m\<ge>n. f m \<longleftrightarrow> f n\<close>
    unfolding n_def
    using q by (rule LeastI [of _ q])
  then have n: \<open>\<And>m. n \<le> m \<Longrightarrow> f m \<longleftrightarrow> f n\<close>
    by blast
  from n_def have n_eq: \<open>(LEAST q. \<forall>m\<ge>q. f m \<longleftrightarrow> f n) = n\<close>
    by (smt (verit, best) Least_le \<open>\<forall>m\<ge>n. f m = f n\<close> dual_order.antisym wellorder_Least_lemma(1))
  show ?thesis
  proof (cases \<open>f n\<close>)
    case False
    with n have *: \<open>\<exists>n. \<forall>n'\<ge>n. \<not> f n'\<close>
      by blast
    have **: \<open>(LEAST n. \<forall>n'\<ge>n. \<not> f n') = n\<close>
      using False n_eq by simp
    from * False show ?thesis
    apply (simp add: set_bits_int_def n_def [symmetric] ** del: upt.upt_Suc)
    apply (auto simp add: take_bit_horner_sum_bit_eq
      bit_horner_sum_bit_iff take_map
      signed_take_bit_def set_bits_int_def
      horner_sum_bit_eq_take_bit simp del: upt.upt_Suc)
    done
  next
    case True
    with n have *: \<open>\<exists>n. \<forall>n'\<ge>n. f n'\<close>
      by blast
    have ***: \<open>\<not> (\<exists>n. \<forall>n'\<ge>n. \<not> f n')\<close>
      apply (rule ccontr)
      using * nat_le_linear by auto
    have **: \<open>(LEAST n. \<forall>n'\<ge>n. f n') = n\<close>
      using True n_eq by simp
    from * *** True show ?thesis
    apply (simp add: set_bits_int_def n_def [symmetric] ** del: upt.upt_Suc)
    apply (auto simp add: take_bit_horner_sum_bit_eq
      bit_horner_sum_bit_iff take_map
      signed_take_bit_def set_bits_int_def
      horner_sum_bit_eq_take_bit nth_append simp del: upt.upt_Suc)
    done
  qed
next
  case False
  then show ?thesis
    by (auto simp add: set_bits_int_def)
qed

inductive wf_set_bits_int :: "(nat \<Rightarrow> bool) \<Rightarrow> bool"
  for f :: "nat \<Rightarrow> bool"
where
  zeros: "\<forall>n' \<ge> n. \<not> f n' \<Longrightarrow> wf_set_bits_int f"
| ones: "\<forall>n' \<ge> n. f n' \<Longrightarrow> wf_set_bits_int f"

lemma wf_set_bits_int_simps: "wf_set_bits_int f \<longleftrightarrow> (\<exists>n. (\<forall>n'\<ge>n. \<not> f n') \<or> (\<forall>n'\<ge>n. f n'))"
by(auto simp add: wf_set_bits_int.simps)

lemma wf_set_bits_int_const [simp]: "wf_set_bits_int (\<lambda>_. b)"
by(cases b)(auto intro: wf_set_bits_int.intros)

lemma wf_set_bits_int_fun_upd [simp]:
  "wf_set_bits_int (f(n := b)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain n'
    where "(\<forall>n''\<ge>n'. \<not> (f(n := b)) n'') \<or> (\<forall>n''\<ge>n'. (f(n := b)) n'')"
    by(auto simp add: wf_set_bits_int_simps)
  hence "(\<forall>n''\<ge>max (Suc n) n'. \<not> f n'') \<or> (\<forall>n''\<ge>max (Suc n) n'. f n'')" by auto
  thus ?rhs by(auto simp only: wf_set_bits_int_simps)
next
  assume ?rhs
  then obtain n' where "(\<forall>n''\<ge>n'. \<not> f n'') \<or> (\<forall>n''\<ge>n'. f n'')" (is "?wf f n'")
    by(auto simp add: wf_set_bits_int_simps)
  hence "?wf (f(n := b)) (max (Suc n) n')" by auto
  thus ?lhs by(auto simp only: wf_set_bits_int_simps)
qed

lemma wf_set_bits_int_Suc [simp]:
  "wf_set_bits_int (\<lambda>n. f (Suc n)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
by(auto simp add: wf_set_bits_int_simps intro: le_SucI dest: Suc_le_D)

context
  fixes f
  assumes wff: "wf_set_bits_int f"
begin

lemma int_set_bits_unfold_BIT:
  "set_bits f = of_bool (f 0) + (2 :: int) * set_bits (f \<circ> Suc)"
using wff proof cases
  case (zeros n)
  show ?thesis
  proof(cases "\<forall>n. \<not> f n")
    case True
    hence "f = (\<lambda>_. False)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "f n'" by blast
    with zeros have "(LEAST n. \<forall>n'\<ge>n. \<not> f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. \<not> f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. \<not> f n') = (\<lambda>n. \<forall>n'\<ge>n. \<not> f (Suc n'))" by(auto dest: Suc_le_D)
    also from zeros have "\<forall>n'\<ge>n. \<not> f (Suc n')" by auto
    ultimately show ?thesis using zeros
      apply (simp (no_asm_simp) add: set_bits_int_unfold' exI
        del: upt.upt_Suc flip: map_map split del: if_split)
      apply (simp only: map_Suc_upt upt_conv_Cons)
      apply simp
      done
  qed
next
  case (ones n)
  show ?thesis
  proof(cases "\<forall>n. f n")
    case True
    hence "f = (\<lambda>_. True)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "\<not> f n'" by blast
    with ones have "(LEAST n. \<forall>n'\<ge>n. f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. f n') = (\<lambda>n. \<forall>n'\<ge>n. f (Suc n'))" by(auto dest: Suc_le_D)
    also from ones have "\<forall>n'\<ge>n. f (Suc n')" by auto
    moreover from ones have "(\<exists>n. \<forall>n'\<ge>n. \<not> f n') = False"
      by(auto intro!: exI[where x="max n m" for n m] simp add: max_def split: if_split_asm)
    moreover hence "(\<exists>n. \<forall>n'\<ge>n. \<not> f (Suc n')) = False"
      by(auto elim: allE[where x="Suc n" for n] dest: Suc_le_D)
    ultimately show ?thesis using ones
      apply (simp (no_asm_simp) add: set_bits_int_unfold' exI split del: if_split)
      apply (auto simp add: Let_def hd_map map_tl[symmetric] map_map[symmetric] map_Suc_upt upt_conv_Cons signed_take_bit_Suc
        not_le simp del: map_map)
      done
  qed
qed

lemma bin_last_set_bits [simp]:
  "odd (set_bits f :: int) = f 0"
  by (subst int_set_bits_unfold_BIT) simp_all

lemma bin_rest_set_bits [simp]:
  "set_bits f div (2 :: int) = set_bits (f \<circ> Suc)"
  by (subst int_set_bits_unfold_BIT) simp_all

lemma bin_nth_set_bits [simp]:
  "bit (set_bits f :: int) m \<longleftrightarrow> f m"
using wff proof (induction m arbitrary: f)
  case 0
  then show ?case
    by (simp add: Bit_Comprehension_Int.bin_last_set_bits bit_0)
next
  case Suc
  from Suc.IH [of "f \<circ> Suc"] Suc.prems show ?case
    by (simp add: Bit_Comprehension_Int.bin_rest_set_bits comp_def bit_Suc)
qed

end

end
