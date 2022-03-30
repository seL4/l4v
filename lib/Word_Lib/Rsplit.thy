(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson and Gerwin Klein, NICTA *)

section \<open>Splitting words into lists\<close>

theory Rsplit
  imports "HOL-Library.Word" More_Word Bits_Int
begin

definition word_rsplit :: "'a::len word \<Rightarrow> 'b::len word list"
  where "word_rsplit w = map word_of_int (bin_rsplit LENGTH('b) (LENGTH('a), uint w))"

lemma word_rsplit_no:
  "(word_rsplit (numeral bin :: 'b::len word) :: 'a word list) =
    map word_of_int (bin_rsplit (LENGTH('a::len))
      (LENGTH('b), take_bit (LENGTH('b)) (numeral bin)))"
  by (simp add: word_rsplit_def of_nat_take_bit)

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

text \<open>
  This odd result arises from the fact that the statement of the
  result implies that the decoded words are of the same type,
  and therefore of the same length, as the original word.\<close>

lemma word_rsplit_same: "word_rsplit w = [w]"
  apply (simp add: word_rsplit_def bin_rsplit_all)
  apply transfer
  apply simp
  done

lemma word_rsplit_empty_iff_size: "word_rsplit w = [] \<longleftrightarrow> size w = 0"
  by (simp add: word_rsplit_def bin_rsplit_def word_size bin_rsplit_aux_simp_alt Let_def
      split: prod.split)

lemma test_bit_rsplit:
  "sw = word_rsplit w \<Longrightarrow> m < size (hd sw) \<Longrightarrow>
    k < length sw \<Longrightarrow> bit (rev sw ! k) m = bit w (k * size (hd sw) + m)"
  for sw :: "'a::len word list"
  apply (unfold word_rsplit_def word_test_bit_def)
  apply (rule trans)
   apply (rule_tac f = "\<lambda>x. bit x m" in arg_cong)
   apply (rule nth_map [symmetric])
   apply simp
  apply (rule bin_nth_rsplit)
     apply simp_all
  apply (simp add : word_size rev_map)
  apply (rule trans)
   defer
   apply (rule map_ident [THEN fun_cong])
  apply (rule refl [THEN map_cong])
  apply (simp add: unsigned_of_int take_bit_int_eq_self_iff)
  using bin_rsplit_size_sign take_bit_int_eq_self_iff by blast

lemma test_bit_rsplit_alt:
  \<open>bit ((word_rsplit w  :: 'b::len word list) ! i) m \<longleftrightarrow>
    bit w ((length (word_rsplit w :: 'b::len word list) - Suc i) * size (hd (word_rsplit w :: 'b::len word list)) + m)\<close>
  if \<open>i < length (word_rsplit w :: 'b::len word list)\<close> \<open>m < size (hd (word_rsplit w :: 'b::len word list))\<close> \<open>0 < length (word_rsplit w :: 'b::len word list)\<close>
  for w :: \<open>'a::len word\<close>
  apply (rule trans)
   apply (rule test_bit_cong)
   apply (rule rev_nth [of _ \<open>rev (word_rsplit w)\<close>, simplified rev_rev_ident])
  apply simp
   apply (rule that(1))
  apply simp
  apply (rule test_bit_rsplit)
    apply (rule refl)
  apply (rule asm_rl)
   apply (rule that(2))
  apply (rule diff_Suc_less)
  apply (rule that(3))
  done

lemma word_rsplit_len_indep [OF refl refl refl refl]:
  "[u,v] = p \<Longrightarrow> [su,sv] = q \<Longrightarrow> word_rsplit u = su \<Longrightarrow>
    word_rsplit v = sv \<Longrightarrow> length su = length sv"
  by (auto simp: word_rsplit_def bin_rsplit_len_indep)

lemma length_word_rsplit_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) \<le> m \<longleftrightarrow> size w \<le> m * n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len_le)

lemmas length_word_rsplit_lt_size =
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len)

lemma length_word_rsplit_even_size:
  "n = LENGTH('a::len) \<Longrightarrow> size w = m * n \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = m"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: length_word_rsplit_exp_size div_nat_eqI)

lemmas length_word_rsplit_exp_size' = refl [THEN length_word_rsplit_exp_size]

\<comment> \<open>alternative proof of \<open>word_rcat_rsplit\<close>\<close>
lemmas tdle = times_div_less_eq_dividend
lemmas dtle = xtrans(4) [OF tdle mult.commute]

lemma word_rcat_rsplit: "word_rcat (word_rsplit w) = w"
  apply (rule word_eqI)
  apply (clarsimp simp: test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
   apply safe
   apply (erule xtrans(7), rule dtle)+
  done

lemma size_word_rsplit_rcat_size:
  "word_rcat ws = frcw \<Longrightarrow> size frcw = length ws * LENGTH('a)
    \<Longrightarrow> length (word_rsplit frcw::'a word list) = length ws"
  for ws :: "'a::len word list" and frcw :: "'b::len word"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: word_size length_word_rsplit_exp_size' div_nat_eqI)

lemma word_rsplit_rcat_size [OF refl]:
  "word_rcat ws = frcw \<Longrightarrow>
    size frcw = length ws * LENGTH('a) \<Longrightarrow> word_rsplit frcw = ws"
  for ws :: "'a::len word list"
  apply (frule size_word_rsplit_rcat_size, assumption)
  apply (clarsimp simp add : word_size)
  apply (rule nth_equalityI, assumption)
  apply clarsimp
  apply (rule word_eqI [rule_format])
  apply (rule trans)
   apply (rule test_bit_rsplit_alt)
     apply (clarsimp simp: word_size)+
  apply (rule trans)
   apply (rule test_bit_rcat [OF refl refl])
  apply (simp add: word_size)
  apply (subst rev_nth)
   apply arith
  apply (simp add: le0 [THEN [2] xtrans(7), THEN diff_Suc_less])
  apply safe
  apply (simp add: diff_mult_distrib)
   apply (cases "size ws")
    apply simp_all
  done

lemma word_rsplit_upt:
  "\<lbrakk> size x = LENGTH('a :: len) * n; n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> word_rsplit x = map (\<lambda>i. ucast (x >> (i * LENGTH('a))) :: 'a word) (rev [0 ..< n])"
  apply (subgoal_tac "length (word_rsplit x :: 'a word list) = n")
   apply (rule nth_equalityI, simp)
   apply (intro allI word_eqI impI)
   apply (simp add: test_bit_rsplit_alt word_size)
   apply (simp add: nth_ucast bit_simps rev_nth field_simps)
  apply (simp add: length_word_rsplit_exp_size word_size)
  apply (subst diff_add_assoc)
   apply (simp flip: less_eq_Suc_le)
  apply simp
  done

end