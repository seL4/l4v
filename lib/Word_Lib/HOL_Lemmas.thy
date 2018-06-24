(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Generic Lemmas used in the Word Library"

theory HOL_Lemmas
imports Main
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
  by (metis atMost_iff le_0_eq le_cases neq0_conv order.strict_trans strict_part_mono_def)

lemma strict_part_mono_reverseE:
  "\<lbrakk> f n \<le> f m; strict_part_mono {.. N :: nat} f; n \<le> N \<rbrakk> \<Longrightarrow> n \<le> m"
  by (rule ccontr) (fastforce simp: linorder_not_le strict_part_mono_def)

lemma takeWhile_take_has_property:
  "n \<le> length (takeWhile P xs) \<Longrightarrow> \<forall>x \<in> set (take n xs). P x"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_take_has_property_nth:
  "\<lbrakk> n < length (takeWhile P xs) \<rbrakk> \<Longrightarrow> P (xs ! n)"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_replicate:
  "takeWhile f (replicate len x) = (if f x then replicate len x else [])"
  by (induct_tac len) auto

lemma takeWhile_replicate_empty:
  "\<not> f x \<Longrightarrow> takeWhile f (replicate len x) = []"
  by (simp add: takeWhile_replicate)

lemma takeWhile_replicate_id:
  "f x \<Longrightarrow> takeWhile f (replicate len x) = replicate len x"
  by (simp add: takeWhile_replicate)

lemma power_sub:
  fixes a :: nat
  assumes lt: "n \<le> m"
  and     av: "0 < a"
  shows "a ^ (m - n) = a ^ m div a ^ n"
proof (subst nat_mult_eq_cancel1 [symmetric])
  show "(0::nat) < a ^ n" using av by simp
next
  from lt obtain q where mv: "n + q = m"
    by (auto simp: le_iff_add)

  have "a ^ n * (a ^ m div a ^ n) = a ^ m"
  proof (subst mult.commute)
    have "a ^ m = (a ^ m div a ^ n) * a ^ n + a ^ m mod a ^ n"
      by (rule  div_mult_mod_eq [symmetric])

    moreover have "a ^ m mod a ^ n = 0"
      by (subst mod_eq_0_iff_dvd, subst dvd_def, rule exI [where x = "a ^ q"],
      (subst power_add [symmetric] mv)+, rule refl)

    ultimately show "(a ^ m div a ^ n) * a ^ n = a ^ m" by simp
  qed

  then show "a ^ n * a ^ (m - n) = a ^ n * (a ^ m div a ^ n)" using lt
    by (simp add: power_add [symmetric])
qed


lemma union_sub:
  "\<lbrakk>B \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> (A - B) \<union> (B - C) = (A - C)"
  by fastforce

lemma insert_sub:
  "x \<in> xs \<Longrightarrow> (insert x (xs - ys)) = (xs - (ys - {x}))"
  by blast

lemma ran_upd:
  "\<lbrakk> inj_on f (dom f); f y = Some z \<rbrakk> \<Longrightarrow> ran (\<lambda>x. if x = y then None else f x) = ran f - {z}"
  unfolding ran_def
  apply (rule set_eqI)
  apply simp
  by (metis domI inj_on_eq_iff option.sel)

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
  by (metis le_add_diff_inverse mult_le_mono2 semiring_normalization_rules(26))

lemma x_power_minus_1:
  fixes x :: "'a :: {ab_group_add, power, numeral, one}"
  shows "x + (2::'a) ^ n - (1::'a) = x + (2 ^ n - 1)" by simp

lemma nat_diff_add:
  fixes i :: nat
  shows "\<lbrakk> i + j = k \<rbrakk> \<Longrightarrow> i = k - j"
  by arith

lemma pow_2_gt: "n \<ge> 2 \<Longrightarrow> (2::int) < 2 ^ n"
  by (induct n) auto

lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x. (P \<longrightarrow> F x) \<and> (\<not> P \<longrightarrow> G x))"
  by simp

lemma case_bool_If:
  "case_bool P Q b = (if b then P else Q)"
  by simp

lemma sum_to_zero:
  "(a :: 'a :: ring) + b = 0 \<Longrightarrow> a = (- b)"
  by (drule arg_cong[where f="\<lambda> x. x - a"], simp)

lemma arith_is_1:
  "\<lbrakk> x \<le> Suc 0; x > 0 \<rbrakk> \<Longrightarrow> x = 1"
  by arith

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemma upt_add_eq_append':
  assumes "i \<le> j" and "j \<le> k"
  shows "[i..<k] = [i..<j] @ [j..<k]"
  using assms le_Suc_ex upt_add_eq_append by blast

lemma split_upt_on_n:
  "n < m \<Longrightarrow> [0 ..< m] = [0 ..< n] @ [n] @ [Suc n ..< m]"
  by (metis append_Cons append_Nil less_Suc_eq_le less_imp_le_nat upt_add_eq_append'
            upt_rec zero_less_Suc)

lemma drop_Suc_nth:
  "n < length xs \<Longrightarrow> drop n xs = xs!n # drop (Suc n) xs"
  by (simp add: Cons_nth_drop_Suc)

lemma n_less_equal_power_2 [simp]:
  "n < 2 ^ n"
  by (induct n; simp)

lemma nat_min_simps [simp]:
  "(a::nat) \<le> b \<Longrightarrow> min b a = a"
  "a \<le> b \<Longrightarrow> min a b = a"
  by auto

lemma power_sub_int:
  "\<lbrakk> m \<le> n; 0 < b \<rbrakk> \<Longrightarrow> b ^ n div b ^ m = (b ^ (n - m) :: int)"
  apply (subgoal_tac "\<exists>n'. n = m + n'")
   apply (clarsimp simp: power_add)
  apply (rule exI[where x="n - m"])
  apply simp
  done

lemma suc_le_pow_2:
  "1 < (n::nat) \<Longrightarrow> Suc n < 2 ^ n"
  by (induct n; clarsimp)
     (case_tac "n = 1"; clarsimp)

lemma nat_le_Suc_less_imp:
  "x < y \<Longrightarrow> x \<le> y - Suc 0"
  by arith

lemma length_takeWhile_less:
  "\<exists>x\<in>set xs. \<not> P x \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (induct xs) (auto split: if_splits)

lemma drop_eq_mono:
  assumes le: "m \<le> n"
  assumes drop: "drop m xs = drop m ys"
  shows "drop n xs = drop n ys"
proof -
  have ex: "\<exists>p. n = p + m" by (rule exI[of _ "n - m"]) (simp add: le)
  then obtain p where p: "n = p + m" by blast
  show ?thesis unfolding p drop_drop[symmetric] drop by simp
qed

lemma nat_Suc_less_le_imp:
  "(k::nat) < Suc n \<Longrightarrow> k \<le> n"
  by auto

lemma nat_add_less_by_max:
  "\<lbrakk> (x::nat) \<le> xmax ; y < k - xmax \<rbrakk> \<Longrightarrow> x + y < k"
  by simp

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  apply (cut_tac m = q and n = c in mod_less_divisor)
  apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
  apply (erule_tac P = "%x. lhs < rhs x" for lhs rhs in ssubst)
  apply (simp add: add_mult_distrib2)
  done

end
