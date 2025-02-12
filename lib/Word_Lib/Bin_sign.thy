(*
 * Copyright Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Bin_sign
  imports
    Main
    "HOL-Library.Word"
    "Word_Lib.Most_significant_bit"
    "Word_Lib.Generic_set_bit"
    "Word_Lib.Reversed_Bit_Lists"
begin

definition bin_sign :: "int \<Rightarrow> int"
  where "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (- 1) = - 1"
  "bin_sign (numeral k) = 0"
  "bin_sign (- numeral k) = -1"
  by (simp_all add: bin_sign_def)

lemma bin_sign_rest [simp]: "bin_sign ((\<lambda>k::int. k div 2) w) = bin_sign w"
  by (simp add: bin_sign_def)

lemma sign_bintr: "bin_sign ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = 0"
  by (simp add: bin_sign_def)

lemma bin_sign_lem: "(bin_sign ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin) = -1) = bit bin n"
  by (simp add: bin_sign_def)

lemma sign_Pls_ge_0: "bin_sign bin = 0 \<longleftrightarrow> bin \<ge> 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma sign_Min_lt_0: "bin_sign bin = -1 \<longleftrightarrow> bin < 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma bin_sign_cat: "bin_sign (concat_bit n y x) = bin_sign x"
  by (simp add: bin_sign_def)

lemma bin_sign_mask [simp]: "bin_sign (mask n) = 0"
  by (simp add: bin_sign_def)

context
  includes bit_operations_syntax
begin

lemma le_int_or: "bin_sign y = 0 \<Longrightarrow> x \<le> x OR y"
  for x y :: int
  by (simp add: bin_sign_def or_greater_eq split: if_splits)

lemma int_and_le: "bin_sign a = 0 \<Longrightarrow> y AND a \<le> a"
  for a y :: int
  by (simp add: bin_sign_def split: if_splits)

lemma bin_sign_and:
  "bin_sign (i AND j) = - (bin_sign i * bin_sign j)"
  by(simp add: bin_sign_def)

lemma bin_nth_minus_p2:
  assumes sign: "bin_sign x = 0"
    and y: "y = push_bit n 1"
    and m: "m < n"
    and x: "x < y"
  shows "bit (x - y) m = bit x m"
proof -
  from \<open>bin_sign x = 0\<close> have \<open>x \<ge> 0\<close>
    by (simp add: sign_Pls_ge_0)
  moreover from x y have \<open>x < 2 ^ n\<close>
    by simp
  ultimately have \<open>q < n\<close> if \<open>bit x q\<close> for q
    using that by (metis bit_take_bit_iff take_bit_int_eq_self)
  then have \<open>bit (x + NOT (mask n)) m = bit x m\<close>
    using \<open>m < n\<close> by (simp add: disjunctive_add bit_simps)
  also have \<open>x + NOT (mask n) = x - y\<close>
    using y by (simp flip: minus_exp_eq_not_mask)
  finally show ?thesis .
qed

end

lemma msb_conv_bin_sign:
  "msb x \<longleftrightarrow> bin_sign x = -1"
  by (simp add: bin_sign_def not_le msb_int_def)

lemma word_msb_def:
  "msb a \<longleftrightarrow> bin_sign (sint a) = - 1"
  by (simp flip: msb_conv_bin_sign add: msb_int_def word_msb_sint)

lemma sign_uint_Pls [simp]: "bin_sign (uint x) = 0"
  by (simp add: sign_Pls_ge_0)

lemma msb_word_def:
  \<open>msb a \<longleftrightarrow> bin_sign (signed_take_bit (LENGTH('a) - 1) (uint a)) = - 1\<close>
  for a :: \<open>'a::len word\<close>
  by (simp add: bin_sign_def bit_simps msb_word_iff_bit)

lemma bin_sign_sc [simp]: "bin_sign (bin_sc n b w) = bin_sign w"
  by (simp add: bin_sign_def set_bit_eq)

lemma sign_bl_bin': "bin_sign (bl_to_bin_aux bs w) = bin_sign w"
  by (induction bs arbitrary: w) (simp_all add: bin_sign_def)

lemma sign_bl_bin: "bin_sign (bl_to_bin bs) = 0"
  by (simp add: bl_to_bin_def sign_bl_bin')

lemma bl_sbin_sign_aux: "hd (bin_to_bl_aux (Suc n) w bs) = (bin_sign (signed_take_bit n w) = -1)"
  by (induction n arbitrary: w bs) (auto simp add: bin_sign_def even_iff_mod_2_eq_zero bit_Suc)

lemma bl_sbin_sign: "hd (bin_to_bl (Suc n) w) = (bin_sign (signed_take_bit n w) = -1)"
  unfolding bin_to_bl_def by (rule bl_sbin_sign_aux)

lemma hd_bl_sign_sint: "hd (to_bl w) = (bin_sign (sint w) = -1)"
  by (simp add: hd_to_bl_iff bit_last_iff bin_sign_def)

end
