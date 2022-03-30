(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Ancient_Numeral
  imports Main Reversed_Bit_Lists Legacy_Aliases
begin

definition Bit :: "int \<Rightarrow> bool \<Rightarrow> int"  (infixl "BIT" 90)
  where "k BIT b = (if b then 1 else 0) + k + k"

lemma Bit_B0: "k BIT False = k + k"
   by (simp add: Bit_def)

lemma Bit_B1: "k BIT True = k + k + 1"
   by (simp add: Bit_def)

lemma Bit_B0_2t: "k BIT False = 2 * k"
  by (rule trans, rule Bit_B0) simp

lemma Bit_B1_2t: "k BIT True = 2 * k + 1"
  by (rule trans, rule Bit_B1) simp

lemma uminus_Bit_eq:
  "- k BIT b = (- k - of_bool b) BIT b"
  by (cases b) (simp_all add: Bit_def)

lemma power_BIT: "2 ^ Suc n - 1 = (2 ^ n - 1) BIT True"
  by (simp add: Bit_B1)

lemma bin_rl_simp [simp]: "bin_rest w BIT bin_last w = w"
  by (simp add: Bit_def)

lemma bin_rest_BIT [simp]: "bin_rest (x BIT b) = x"
  by (simp add: Bit_def)

lemma even_BIT [simp]: "even (x BIT b) \<longleftrightarrow> \<not> b"
  by (simp add: Bit_def)

lemma bin_last_BIT [simp]: "bin_last (x BIT b) = b"
  by simp

lemma BIT_eq_iff [iff]: "u BIT b = v BIT c \<longleftrightarrow> u = v \<and> b = c"
  by (auto simp: Bit_def) arith+

lemma BIT_bin_simps [simp]:
  "numeral k BIT False = numeral (Num.Bit0 k)"
  "numeral k BIT True = numeral (Num.Bit1 k)"
  "(- numeral k) BIT False = - numeral (Num.Bit0 k)"
  "(- numeral k) BIT True = - numeral (Num.BitM k)"
  by (simp_all only: Bit_B0 Bit_B1 numeral.simps numeral_BitM)

lemma BIT_special_simps [simp]:
  shows "0 BIT False = 0"
    and "0 BIT True = 1"
    and "1 BIT False = 2"
    and "1 BIT True = 3"
    and "(- 1) BIT False = - 2"
    and "(- 1) BIT True = - 1"
  by (simp_all add: Bit_def)

lemma Bit_eq_0_iff: "w BIT b = 0 \<longleftrightarrow> w = 0 \<and> \<not> b"
  by (auto simp: Bit_def) arith

lemma Bit_eq_m1_iff: "w BIT b = -1 \<longleftrightarrow> w = -1 \<and> b"
  by (auto simp: Bit_def) arith

lemma expand_BIT:
  "numeral (Num.Bit0 w) = numeral w BIT False"
  "numeral (Num.Bit1 w) = numeral w BIT True"
  "- numeral (Num.Bit0 w) = (- numeral w) BIT False"
  "- numeral (Num.Bit1 w) = (- numeral (w + Num.One)) BIT True"
  by (simp_all add: BitM_inc_eq add_One)

lemma less_Bits: "v BIT b < w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> \<not> b \<and> c"
  by (auto simp: Bit_def)

lemma le_Bits: "v BIT b \<le> w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> (\<not> b \<or> c)"
  by (auto simp: Bit_def)

lemma pred_BIT_simps [simp]:
  "x BIT False - 1 = (x - 1) BIT True"
  "x BIT True - 1 = x BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma succ_BIT_simps [simp]:
  "x BIT False + 1 = x BIT True"
  "x BIT True + 1 = (x + 1) BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma add_BIT_simps [simp]:
  "x BIT False + y BIT False = (x + y) BIT False"
  "x BIT False + y BIT True = (x + y) BIT True"
  "x BIT True + y BIT False = (x + y) BIT True"
  "x BIT True + y BIT True = (x + y + 1) BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma mult_BIT_simps [simp]:
  "x BIT False * y = (x * y) BIT False"
  "x * y BIT False = (x * y) BIT False"
  "x BIT True * y = (x * y) BIT False + y"
  by (simp_all add: Bit_B0_2t Bit_B1_2t algebra_simps)

lemma B_mod_2': "X = 2 \<Longrightarrow> (w BIT True) mod X = 1 \<and> (w BIT False) mod X = 0"
  by (simp add: Bit_B0 Bit_B1)

lemma bin_ex_rl: "\<exists>w b. w BIT b = bin"
  by (metis bin_rl_simp)

lemma bin_exhaust: "(\<And>x b. bin = x BIT b \<Longrightarrow> Q) \<Longrightarrow> Q"
by (metis bin_ex_rl)

lemma bin_abs_lem: "bin = (w BIT b) \<Longrightarrow> bin \<noteq> -1 \<longrightarrow> bin \<noteq> 0 \<longrightarrow> nat \<bar>w\<bar> < nat \<bar>bin\<bar>"
  apply clarsimp
  apply (unfold Bit_def)
  apply (cases b)
   apply (clarsimp, arith)
  apply (clarsimp, arith)
  done

lemma bin_induct:
  assumes PPls: "P 0"
    and PMin: "P (- 1)"
    and PBit: "\<And>bin bit. P bin \<Longrightarrow> P (bin BIT bit)"
  shows "P bin"
  apply (rule_tac P=P and a=bin and f1="nat \<circ> abs" in wf_measure [THEN wf_induct])
  apply (simp add: measure_def inv_image_def)
  apply (case_tac x rule: bin_exhaust)
  apply (frule bin_abs_lem)
  apply (auto simp add : PPls PMin PBit)
  done

lemma Bit_div2: "(w BIT b) div 2 = w"
  by (fact bin_rest_BIT)

lemma twice_conv_BIT: "2 * x = x BIT False"
  by (simp add: Bit_def)

lemma BIT_lt0 [simp]: "x BIT b < 0 \<longleftrightarrow> x < 0"
by(cases b)(auto simp add: Bit_def)

lemma BIT_ge0 [simp]: "x BIT b \<ge> 0 \<longleftrightarrow> x \<ge> 0"
by(cases b)(auto simp add: Bit_def)

lemma bin_to_bl_aux_Bit_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n (w BIT b) bl = bin_to_bl_aux (n - 1) w (b # bl)"
  by (cases n) auto

lemma bl_to_bin_BIT:
  "bl_to_bin bs BIT b = bl_to_bin (bs @ [b])"
  by (simp add: bl_to_bin_append Bit_def)

lemma bin_nth_0_BIT: "bin_nth (w BIT b) 0 \<longleftrightarrow> b"
  by simp

lemma bin_nth_Suc_BIT: "bin_nth (w BIT b) (Suc n) = bin_nth w n"
  by (simp add: bit_Suc)

lemma bin_nth_minus [simp]: "0 < n \<Longrightarrow> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) (simp_all add: bit_Suc)

lemma bin_sign_simps [simp]:
  "bin_sign (w BIT b) = bin_sign w"
  by (simp add: bin_sign_def Bit_def)

lemma bin_nth_Bit: "bin_nth (w BIT b) n \<longleftrightarrow> n = 0 \<and> b \<or> (\<exists>m. n = Suc m \<and> bin_nth w m)"
  by (cases n) auto

lemmas sbintrunc_Suc_BIT [simp] =
  signed_take_bit_Suc [where a="w BIT b", simplified bin_last_BIT bin_rest_BIT] for w b

lemmas sbintrunc_0_BIT_B0 [simp] =
  signed_take_bit_0 [where a="w BIT False", simplified bin_last_numeral_simps bin_rest_numeral_simps]
  for w

lemmas sbintrunc_0_BIT_B1 [simp] =
  signed_take_bit_0 [where a="w BIT True", simplified bin_last_BIT bin_rest_numeral_simps]
  for w

lemma sbintrunc_Suc_minus_Is:
  \<open>0 < n \<Longrightarrow>
  sbintrunc (n - 1) w = y \<Longrightarrow>
  sbintrunc n (w BIT b) = y BIT b\<close>
  by (cases n) (simp_all add: Bit_def signed_take_bit_Suc)

lemma bin_cat_Suc_Bit: "bin_cat w (Suc n) (v BIT b) = bin_cat w n v BIT b"
  by (auto simp add: Bit_def concat_bit_Suc)

context
  includes bit_operations_syntax
begin

lemma int_not_BIT [simp]: "NOT (w BIT b) = (NOT w) BIT (\<not> b)"
  by (simp add: not_int_def Bit_def)

lemma int_and_Bits [simp]: "(x BIT b) AND (y BIT c) = (x AND y) BIT (b \<and> c)"
  using and_int_rec [of \<open>x BIT b\<close> \<open>y BIT c\<close>] by (auto simp add: Bit_B0_2t Bit_B1_2t)

lemma int_or_Bits [simp]: "(x BIT b) OR (y BIT c) = (x OR y) BIT (b \<or> c)"
  using or_int_rec [of \<open>x BIT b\<close> \<open>y BIT c\<close>] by (auto simp add: Bit_B0_2t Bit_B1_2t)

lemma int_xor_Bits [simp]: "(x BIT b) XOR (y BIT c) = (x XOR y) BIT ((b \<or> c) \<and> \<not> (b \<and> c))"
  using xor_int_rec [of \<open>x BIT b\<close> \<open>y BIT c\<close>] by (auto simp add: Bit_B0_2t Bit_B1_2t)

end

lemma mod_BIT:
  "bin BIT bit mod 2 ^ Suc n = (bin mod 2 ^ n) BIT bit" for bit
proof -
  have "2 * (bin mod 2 ^ n) + 1 = (2 * bin mod 2 ^ Suc n) + 1"
    by (simp add: mod_mult_mult1)
  also have "\<dots> = ((2 * bin mod 2 ^ Suc n) + 1) mod 2 ^ Suc n"
    by (simp add: ac_simps pos_zmod_mult_2)
  also have "\<dots> = (2 * bin + 1) mod 2 ^ Suc n"
    by (simp only: mod_simps)
  finally show ?thesis
    by (auto simp add: Bit_def)
qed

lemma minus_BIT_0: fixes x y :: int shows "x BIT b - y BIT False = (x - y) BIT b"
by(simp add: Bit_def)

lemma int_lsb_BIT [simp]: fixes x :: int shows
  "lsb (x BIT b) \<longleftrightarrow> b"
by(simp add: lsb_int_def)

lemma int_shiftr_BIT [simp]: fixes x :: int
  shows int_shiftr0: "drop_bit 0 x = x"
  and int_shiftr_Suc: "drop_bit (Suc n) (x BIT b) = drop_bit n x"
  by (simp_all add: drop_bit_Suc)

lemma msb_BIT [simp]: "msb (x BIT b) = msb x"
by(simp add: msb_int_def)

end