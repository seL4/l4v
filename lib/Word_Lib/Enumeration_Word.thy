(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Thomas Sewell *)

section "Enumeration Instances for Words"

theory Enumeration_Word
  imports
    "HOL-Library.Word"
    More_Word
    Enumeration
    Even_More_List
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
  upto_enum_step :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word list" ("[_ , _ .e. _]")
where
  "upto_enum_step a b c \<equiv>
      if c < a then [] else map (\<lambda>x. a + x * (b - a)) [0 .e. (c - a) div (b - a)]"
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

  show ?thesis
    apply (subst upto_enum_red)
    apply (simp del: upt.simps)
    apply (subst Suc_unat_diff_1 [OF lt])
    apply (rule map_cong [OF refl])
    apply (rule toEnum_of_nat)
    apply simp
    apply (erule order_less_trans [OF _ lt'])
    done
qed

lemma upto_enum_red2:
  assumes szv: "sz < LENGTH('a :: len)"
  shows "[(0:: 'a :: len word) .e. 2 ^ sz - 1] =
  map of_nat [0 ..< 2 ^ sz]" using szv
  apply (subst unat_power_lower[OF szv, symmetric])
  apply (rule upto_enum_red')
  apply (subst word_le_nat_alt, simp)
  done

lemma upto_enum_step_red:
  assumes szv: "sz < LENGTH('a)"
  and   usszv: "us \<le> sz"
  shows "[0 :: 'a :: len word , 2 ^ us .e. 2 ^ sz - 1] =
  map (\<lambda>x. of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]" using szv
  unfolding upto_enum_step_def
  apply (subst if_not_P)
   apply (rule leD)
   apply (subst word_le_nat_alt)
   apply (subst unat_minus_one)
    apply simp
   apply simp
  apply simp
  apply (subst upto_enum_red)
  apply (simp del: upt.simps)
  apply (subst Suc_div_unat_helper [where 'a = 'a, OF szv usszv, symmetric])
  apply clarsimp
  apply (subst toEnum_of_nat)
   apply (erule order_less_trans)
   using szv
   apply simp
  apply simp
  done

lemma upto_enum_word:
  "[x .e. y] = map of_nat [unat x ..< Suc (unat y)]"
  apply (subst upto_enum_red)
  apply clarsimp
  apply (subst toEnum_of_nat)
   prefer 2
   apply (rule refl)
  apply (erule disjE, simp)
  apply clarsimp
  apply (erule order_less_trans)
  apply simp
  done

lemma word_upto_Cons_eq:
  "x < y \<Longrightarrow> [x::'a::len word .e. y] = x # [x + 1 .e. y]"
  apply (subst upto_enum_red)
  apply (subst upt_conv_Cons)
  apply simp_all
   apply unat_arith
  apply (simp only: list.map list.inject upto_enum_red to_from_enum simp_thms)
  apply simp_all
  apply unat_arith
  done

lemma distinct_enum_upto:
  "distinct [(0 :: 'a::len word) .e. b]"
proof -
  have "\<And>(b::'a word). [0 .e. b] = nths enum {..< Suc (fromEnum b)}"
    apply (subst upto_enum_red)
    apply (subst nths_upt_eq_take)
    apply (subst enum_word_def)
    apply (subst take_map)
    apply (subst take_upt)
     apply (simp only: add_0 fromEnum_unat)
     apply (rule order_trans [OF _ order_eq_refl])
      apply (rule Suc_leI [OF unat_lt2p])
     apply simp
    apply clarsimp
    apply (rule toEnum_of_nat)
    apply (erule order_less_trans [OF _ unat_lt2p])
    done

  then show ?thesis
    by (rule ssubst) (rule distinct_nthsI, simp)
qed

lemma upto_enum_set_conv [simp]:
  fixes a :: "'a :: len word"
  shows "set [a .e. b] = {x. a \<le> x \<and> x \<le> b}"
  apply (subst upto_enum_red)
  apply (subst set_map)
  apply safe
    apply simp
    apply clarsimp
    apply (erule disjE)
     apply simp
     apply (erule iffD2 [OF word_le_nat_alt])
    apply clarsimp
  apply simp_all
    apply (metis le_unat_uoi nat_less_le toEnum_of_nat unsigned_less word_le_nat_alt)
   apply (metis le_unat_uoi less_or_eq_imp_le toEnum_of_nat unsigned_less word_le_nat_alt)
    apply (rule_tac x="fromEnum x" in image_eqI)
   apply clarsimp
  apply clarsimp
  apply transfer
  apply auto
  done

lemma upto_enum_less:
  assumes xin: "x \<in> set [(a::'a::len word).e.2 ^ n - 1]"
  and     nv:  "n < LENGTH('a::len)"
  shows   "x < 2 ^ n"
proof (cases n)
  case 0
  then show ?thesis using xin by simp
next
  case (Suc m)
  show ?thesis using xin nv le_m1_iff_lt p2_gt_0 by auto
qed

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
  by (subst word_upto_Cons_eq, auto, fact+)

lemma upto_enum_set_conv2:
  fixes a :: "'a::len word"
  shows "set [a .e. b] = {a .. b}"
  by auto

lemma length_upto_enum [simp]:
  fixes a :: "'a :: len word"
  shows "length [a .e. b] = Suc (unat b) - unat a"
  apply (simp add: word_le_nat_alt upto_enum_red)
  apply (clarsimp simp: Suc_diff_le)
  done

lemma length_upto_enum_cases:
  fixes a :: "'a::len word"
  shows "length [a .e. b] = (if a \<le> b then Suc (unat b) - unat a else 0)"
  apply (case_tac "a \<le> b")
   apply (clarsimp)
  apply (clarsimp simp: upto_enum_def)
  apply unat_arith
  done

lemma length_upto_enum_less_one:
  "\<lbrakk>a \<le> b; b \<noteq> 0\<rbrakk>
  \<Longrightarrow> length [a .e. b - 1] = unat (b - a)"
  apply clarsimp
  apply (subst unat_sub[symmetric], assumption)
  apply clarsimp
  done

lemma drop_upto_enum:
  "drop (unat n) [0 .e. m] = [n .e. m]"
  apply (clarsimp simp: upto_enum_def)
  apply (induct m, simp)
  by (metis drop_map drop_upt plus_nat.add_0)

lemma distinct_enum_upto' [simp]:
  "distinct [a::'a::len word .e. b]"
  apply (subst drop_upto_enum [symmetric])
  apply (rule distinct_drop)
  apply (rule distinct_enum_upto)
  done

lemma length_interval:
  "\<lbrakk>set xs = {x. (a::'a::len word) \<le> x \<and> x \<le> b}; distinct xs\<rbrakk>
  \<Longrightarrow> length xs = Suc (unat b) - unat a"
  apply (frule distinct_card)
  apply (subgoal_tac "set xs = set [a .e. b]")
   apply (cut_tac distinct_card [where xs="[a .e. b]"])
    apply (subst (asm) length_upto_enum)
    apply clarsimp
   apply (rule distinct_enum_upto')
  apply simp
  done

lemma enum_word_div:
  fixes v :: "'a :: len word" shows
  "\<exists>xs ys. enum = xs @ [v] @ ys
             \<and> (\<forall>x \<in> set xs. x < v)
             \<and> (\<forall>y \<in> set ys. v < y)"
  apply (simp only: enum_word_def)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule order_less_imp_le, simp)
  apply (simp add: upt_conv_Cons)
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a='a])
    apply simp
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (drule of_nat_mono_maybe[rotated, where 'a='a])
   apply simp
  apply simp
  done

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
