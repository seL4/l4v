(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Thomas Sewell *)

section "Enumeration Instances for Words"

theory Enumeration_Word
  imports More_Word Enumeration Even_More_List
begin

lemma length_word_enum: "length (enum :: 'a :: len word list) = 2 ^ LENGTH('a)"
  by (simp add: enum_word_def)

lemma fromEnum_unat[simp]: "fromEnum (x :: 'a::len word) = unat x"
proof -
  have "enum ! the_index enum x = x" by (auto intro: nth_the_index)
  moreover
  have "the_index enum x < length (enum::'a::len word list)" by (auto intro: the_index_bounded)
  moreover
  { fix y assume "of_nat y = x"
    moreover assume "y < 2 ^ LENGTH('a)"
    ultimately have "y = unat x" using of_nat_inverse by fastforce
  }
  ultimately
  show ?thesis by (simp add: fromEnum_def enum_word_def)
qed

lemma toEnum_of_nat[simp]: "n < 2 ^ LENGTH('a) \<Longrightarrow> (toEnum n :: 'a :: len word) = of_nat n"
  by (simp add: toEnum_def length_word_enum enum_word_def)

instantiation word :: (len) enumeration_both
begin

definition
  enum_alt_word_def: "enum_alt \<equiv> alt_from_ord (enum :: ('a :: len) word list)"

instance
  by (intro_classes, simp add: enum_alt_word_def)

end

definition
  upto_enum_step :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word list"
    (\<open>(\<open>notation=\<open>mixfix upto_enum_step\<close>\<close>[_ , _ .e. _])\<close>)
where
  "[a , b .e. c] \<equiv> if c < a then [] else map (\<lambda>x. a + x * (b - a)) [0 .e. (c - a) div (b - a)]"
  (* in the wraparound case, bad things happen. *)

lemma maxBound_word:
  "(maxBound::'a::len word) = -1"
  by (simp add: maxBound_def enum_word_def last_map of_nat_diff)

lemma minBound_word:
  "(minBound::'a::len word) = 0"
  by (simp add: minBound_def enum_word_def upt_conv_Cons)

lemma maxBound_max_word:
  "(maxBound::'a::len word) = - 1"
  by (fact maxBound_word)

lemma leq_maxBound [simp]:
  "(x::'a::len word) \<le> maxBound"
  by (simp add: maxBound_max_word)

lemma upto_enum_red':
  assumes lt: "1 \<le> X"
  shows "[(0::'a :: len word) .e. X - 1] =  map of_nat [0 ..< unat X]"
proof -
  have lt': "unat X < 2 ^ LENGTH('a)"
    by (rule unat_lt2p)
  have "map (toEnum::nat \<Rightarrow> 'a word) [0..<unat X] = map word_of_nat [0..<unat X]"
    using order_less_trans by fastforce
  then show ?thesis
    by (simp add: Suc_unat_diff_1 lt upto_enum_red)
qed

lemma upto_enum_red2:
  assumes szv: "sz < LENGTH('a :: len)"
  shows "[(0:: 'a :: len word) .e. 2 ^ sz - 1] =
  map of_nat [0 ..< 2 ^ sz]" using szv
  by (simp add: upto_enum_red' word_1_le_power)

lemma upto_enum_step_red:
  assumes szv: "sz < LENGTH('a)"
  and   usszv: "us \<le> sz"
  shows "[0 :: 'a :: len word , 2 ^ us .e. 2 ^ sz - 1]
       = map (\<lambda>x. of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]"
proof -
  have "\<And>n. \<lbrakk>n < 2 ^ (sz - us)\<rbrakk> \<Longrightarrow> toEnum n * 2 ^ us = (word_of_nat n * 2 ^ us :: 'a word)"
    using szv nat_less_le order_le_less_trans by fastforce
  with assms show ?thesis
    by (simp add: upto_enum_step_def upto_enum_red Suc_div_unat_helper)
qed

lemma upto_enum_word: "[x .e. y] = map of_nat [unat x ..< Suc (unat y)]"
  unfolding upto_enum_red
  using order_less_trans toEnum_of_nat by force

lemma word_upto_Cons_eq:
  "x < y \<Longrightarrow> [x::'a::len word .e. y] = x # [x + 1 .e. y]"
  unfolding upto_enum_red
  using lessI less_is_non_zero_p1 unatSuc2 unat_mono upt_conv_Cons by fastforce

lemma distinct_enum_upto:
  "distinct [(0 :: 'a::len word) .e. b]"
proof -
  have "\<And>(b::'a word). [0 .e. b] = nths enum {..< Suc (fromEnum b)}"
    unfolding upto_enum_red nths_upt_eq_take enum_word_def
    using order_less_trans toEnum_of_nat
    by (fastforce simp: take_map Suc_leI)
  then show ?thesis
    by (rule ssubst) (rule distinct_nthsI, simp)
qed

lemma upto_enum_set_conv [simp]:
  fixes a :: "'a :: len word"
  shows "set [a .e. b] = {x. a \<le> x \<and> x \<le> b}"
proof -
  have "a \<le> b"
    if "unat a \<le> unat b"
    using that word_less_eq_iff_unsigned by blast
  moreover have "a \<le> toEnum m"
    if "unat a \<le> m" "m < unat b" for m
    using that
    by (metis fromEnum_unat le_unat_uoi nat_less_le to_from_enum word_le_nat_alt)
  moreover have "toEnum n \<le> b"
    if "unat a \<le> n" "n < unat b" for n
    using that
    by (metis fromEnum_unat le_unat_uoi nat_less_le to_from_enum word_of_nat_le)
  moreover have "w \<in> toEnum ` {x. unat a \<le> unat b \<and> (x = unat b \<or> unat a \<le> x \<and> x < unat b)}"
    if "a \<le> w" and "w \<le> b" for w :: "'a word"
    using that
    by (smt (verit, del_insts) order.order_iff_strict order.trans fromEnum_unat imageI mem_Collect_eq to_from_enum unat_mono)
  ultimately show ?thesis
    by (auto simp: upto_enum_red)
qed

lemma upto_enum_less:
  assumes "x \<in> set [(a::'a::len word).e.2 ^ n - 1]" and "n < LENGTH('a::len)"
  shows   "x < 2 ^ n"
  using assms by auto

lemma upto_enum_len_less:
  "\<lbrakk> n \<le> length [a, b .e. c]; n \<noteq> 0 \<rbrakk> \<Longrightarrow> a \<le> c"
  unfolding upto_enum_step_def
  by (simp split: if_split_asm)

lemma length_upto_enum_step:
  fixes x :: "'a :: len word"
  shows "x \<le> z \<Longrightarrow> length [x , y .e. z] = (unat ((z - x) div (y - x))) + 1"
  unfolding upto_enum_step_def
  by (simp add: upto_enum_red)

lemma map_length_unfold_one:
  fixes x :: "'a::len word"
  assumes xv: "Suc (unat x) < 2 ^ LENGTH('a)"
  and     ax: "a < x"
  shows   "map f [a .e. x] = f a # map f [a + 1 .e. x]"
  by (simp add: ax word_upto_Cons_eq)

lemma upto_enum_set_conv2:
  fixes a :: "'a::len word"
  shows "set [a .e. b] = {a .. b}"
  by auto

lemma length_upto_enum [simp]:
  fixes a :: "'a :: len word"
  shows "length [a .e. b] = Suc (unat b) - unat a"
  by (metis length_map length_upt upto_enum_word)

lemma length_upto_enum_cases:
  fixes a :: "'a::len word"
  shows "length [a .e. b] = (if a \<le> b then Suc (unat b) - unat a else 0)"
  by (simp add: word_le_nat_alt)

lemma length_upto_enum_less_one:
  "\<lbrakk>a \<le> b; b \<noteq> 0\<rbrakk> \<Longrightarrow> length [a .e. b - 1] = unat (b - a)"
  by (simp add: unat_sub)

lemma drop_upto_enum: "drop (unat n) [0 .e. m] = [n .e. m]"
  by (induction m) (auto simp: upto_enum_def drop_map)

lemma distinct_enum_upto' [simp]:
  "distinct [a::'a::len word .e. b]"
  by (metis distinct_drop distinct_enum_upto drop_upto_enum)

lemma length_interval:
  "\<lbrakk>set xs = {x. (a::'a::len word) \<le> x \<and> x \<le> b}; distinct xs\<rbrakk>
  \<Longrightarrow> length xs = Suc (unat b) - unat a"
  by (metis distinct_card distinct_enum_upto' length_upto_enum upto_enum_set_conv)

lemma enum_word_div:
  fixes v :: "'a :: len word"
  shows "\<exists>xs ys. enum = xs @ [v] @ ys \<and> (\<forall>x \<in> set xs. x < v) \<and> (\<forall>y \<in> set ys. v < y)"
proof -
  have \<section>: "[0..<2 ^ LENGTH('a)] = ([0..<unat v] @ [unat v..<2 ^ LENGTH('a)])"
    by (simp add: order_less_imp_le upt_add_eq_append')
  have "\<And>n. \<lbrakk>unat v < n; n < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> v < word_of_nat n"
    using unat_ucast_less_no_overflow by blast
  moreover
  have "\<forall>w\<in>set (map word_of_nat [0..<unat v]). w < v"
    using word_of_nat_less by force
  ultimately show ?thesis
    unfolding enum_word_def order_less_imp_le upt_add_eq_append' \<section>
    by (force simp add: upt_conv_Cons)
qed

lemma remdups_enum_upto:
  fixes s::"'a::len word"
  shows "remdups [s .e. e] = [s .e. e]"
  by simp

lemma card_enum_upto:
  fixes s::"'a::len word"
  shows "card (set [s .e. e]) = Suc (unat e) - unat s"
  by (subst List.card_set) (simp add: remdups_enum_upto)

lemma length_upto_enum_one:
  fixes x :: "'a :: len word"
  assumes lt1: "x < y" and lt2: "z < y" and lt3: "x \<le> z"
  shows "[x , y .e. z] = [x]"
  unfolding upto_enum_step_def
proof (subst upto_enum_red, subst if_not_P [OF leD [OF lt3]], clarsimp, rule conjI)
  show "unat ((z - x) div (y - x)) = 0"
  proof (subst unat_div, rule div_less)
    have syx: "unat (y - x) = unat y - unat x"
      by (rule unat_sub [OF order_less_imp_le]) fact
    moreover have "unat (z - x) = unat z - unat x"
      by (rule unat_sub) fact

    ultimately show "unat (z - x) < unat (y - x)"
      using lt2 lt3 unat_mono word_less_minus_mono_left by blast
  qed

  then show "(z - x) div (y - x) * (y - x) = 0"
    by (simp add: unat_div) (simp add: word_arith_nat_defs(6))
qed

end
