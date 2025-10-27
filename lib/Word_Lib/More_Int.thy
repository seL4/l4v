(*
 * Copyright Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>More on bitwise operations on integers\<close>

theory More_Int
  imports Main
begin

(* FIXME: move to Word distribution? *)
lemma bin_nth_minus_Bit0[simp]:
  "0 < n \<Longrightarrow> bit (numeral (num.Bit0 w) :: int) n = bit (numeral w :: int) (n - 1)"
  by (cases n; simp)

lemma bin_nth_minus_Bit1[simp]:
  "0 < n \<Longrightarrow> bit (numeral (num.Bit1 w) :: int) n = bit (numeral w :: int) (n - 1)"
  by (cases n; simp)

lemma bin_cat_eq_push_bit_add_take_bit:
  \<open>concat_bit n l k = push_bit n k + take_bit n l\<close>
  by (simp add: concat_bit_eq)

lemma bin_cat_assoc: "(\<lambda>k n l. concat_bit n l k) ((\<lambda>k n l. concat_bit n l k) x m y) n z = (\<lambda>k n l. concat_bit n l k) x (m + n) ((\<lambda>k n l. concat_bit n l k) y n z)"
  by (fact concat_bit_assoc)

lemma bin_cat_assoc_sym: "(\<lambda>k n l. concat_bit n l k) x m ((\<lambda>k n l. concat_bit n l k) y n z) = (\<lambda>k n l. concat_bit n l k) ((\<lambda>k n l. concat_bit n l k) x (m - n) y) (min m n) z"
  by (fact concat_bit_assoc_sym)

lemma bin_nth_cat:
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) ((\<lambda>k n l. concat_bit n l k) x k y) n =
    (if n < k then (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n else (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x (n - k))"
  by (simp add: bit_concat_bit_iff)

lemma bin_nth_drop_bit_iff:
  \<open>(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (drop_bit n c) k \<longleftrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c (n + k)\<close>
  by (simp add: bit_drop_bit_eq)

lemma bin_nth_take_bit_iff:
  \<open>(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (take_bit n c) k \<longleftrightarrow> k < n \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c k\<close>
  by (fact bit_take_bit_iff)

lemma bin_cat_zero [simp]: "(\<lambda>k n l. concat_bit n l k) 0 n w = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma bintr_cat1: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (k + n) ((\<lambda>k n l. concat_bit n l k) a n b) = (\<lambda>k n l. concat_bit n l k) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) k a) n b"
  by (metis bin_cat_assoc bin_cat_zero)

lemma bintr_cat: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((\<lambda>k n l. concat_bit n l k) a n b) =
    (\<lambda>k n l. concat_bit n l k) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (m - n) a) n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (min m n) b)"
  by (rule bit_eqI) (auto simp add: bit_simps)

lemma bintr_cat_same [simp]: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((\<lambda>k n l. concat_bit n l k) a n b) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: "(\<lambda>k n l. concat_bit n l k) a n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n b) = (\<lambda>k n l. concat_bit n l k) a n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma drop_bit_bin_cat_eq:
  \<open>drop_bit n ((\<lambda>k n l. concat_bit n l k) v n w) = v\<close>
  by (rule bit_eqI) (simp add: bit_drop_bit_eq bit_concat_bit_iff)

lemma take_bit_bin_cat_eq:
  \<open>take_bit n ((\<lambda>k n l. concat_bit n l k) v n w) = take_bit n w\<close>
  by (rule bit_eqI) (simp add: bit_concat_bit_iff)

lemma bin_cat_num: "(\<lambda>k n l. concat_bit n l k) a n b = a * 2 ^ n + (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit push_bit_eq_mult)

lemma bin_cat_cong: "concat_bit n b a = concat_bit m d c"
  if "n = m" "a = c" "take_bit m b = take_bit m d"
  using that(3) unfolding that(1,2)
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma bin_cat_eqD1: "concat_bit n b a = concat_bit n d c \<Longrightarrow> a = c"
  by (metis drop_bit_bin_cat_eq)

lemma bin_cat_eqD2: "concat_bit n b a = concat_bit n d c \<Longrightarrow> take_bit n b = take_bit n d"
  by (metis take_bit_bin_cat_eq)

lemma bin_cat_inj: "(concat_bit n b a) = concat_bit n d c \<longleftrightarrow> a = c \<and> take_bit n b = take_bit n d"
  by (auto intro: bin_cat_cong bin_cat_eqD1 bin_cat_eqD2)

lemma bin_last_def:
  "(odd :: int \<Rightarrow> bool) w \<longleftrightarrow> w mod 2 = 1"
  by (fact odd_iff_mod_2_eq_one)

lemma bin_last_numeral_simps [simp]:
  "\<not> odd (0 :: int)"
  "odd (1 :: int)"
  "odd (- 1 :: int)"
  "odd (Numeral1 :: int)"
  "\<not> odd (numeral (Num.Bit0 w) :: int)"
  "odd (numeral (Num.Bit1 w) :: int)"
  "\<not> odd (- numeral (Num.Bit0 w) :: int)"
  "odd (- numeral (Num.Bit1 w) :: int)"
  by simp_all

lemma bin_rest_numeral_simps [simp]:
  "(\<lambda>k::int. k div 2) 0 = 0"
  "(\<lambda>k::int. k div 2) 1 = 0"
  "(\<lambda>k::int. k div 2) (- 1) = - 1"
  "(\<lambda>k::int. k div 2) Numeral1 = 0"
  "(\<lambda>k::int. k div 2) (numeral (Num.Bit0 w)) = numeral w"
  "(\<lambda>k::int. k div 2) (numeral (Num.Bit1 w)) = numeral w"
  "(\<lambda>k::int. k div 2) (- numeral (Num.Bit0 w)) = - numeral w"
  "(\<lambda>k::int. k div 2) (- numeral (Num.Bit1 w)) = - numeral (w + Num.One)"
  by simp_all

lemma bin_rl_eqI: "\<lbrakk>(\<lambda>k::int. k div 2) x = (\<lambda>k::int. k div 2) y; odd x = odd y\<rbrakk> \<Longrightarrow> x = y"
  by (auto elim: oddE)

lemma [simp]:
  shows bin_rest_lt0: "(\<lambda>k::int. k div 2) i < 0 \<longleftrightarrow> i < 0"
  and  bin_rest_ge_0: "(\<lambda>k::int. k div 2) i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by auto

lemma bin_rest_gt_0 [simp]: "(\<lambda>k::int. k div 2) x > 0 \<longleftrightarrow> x > 1"
  by auto

lemma bin_nth_eq_iff: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) x = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y \<longleftrightarrow> x = y"
  by (simp add: bit_eq_iff fun_eq_iff)

lemma bin_eqI:
  "x = y" if "\<And>n. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n \<longleftrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n"
  using that by (rule bit_eqI)

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n)"
  by (metis bit_eq_iff)

lemma bin_nth_zero [simp]: "\<not> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) 0 n"
  by simp

lemma bin_nth_1 [simp]: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) 1 n \<longleftrightarrow> n = 0"
  by (cases n) (simp_all add: bit_Suc)

lemma bin_nth_minus1 [simp]: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (- 1) n"
  by simp

lemma bin_nth_numeral: "(\<lambda>k::int. k div 2) x = y \<Longrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x (numeral n) = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y (pred_numeral n)"
  by (simp add: numeral_eq_Suc bit_Suc)

lemmas bin_nth_numeral_simps [simp] =
  bin_nth_numeral [OF bin_rest_numeral_simps(8)]

lemmas bin_nth_simps =
  bit_0 bit_Suc bin_nth_zero bin_nth_minus1
  bin_nth_numeral_simps

lemma nth_2p_bin: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (2 ^ n) m = (m = n)" \<comment> \<open>for use when simplifying with \<open>bin_nth_Bit\<close>\<close>
  by (auto simp add: bit_exp_iff)

lemma nth_rest_power_bin: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (((\<lambda>k::int. k div 2) ^^ k) w) n = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w (n + k)"
  by (induct k arbitrary: n) (auto simp flip: bit_Suc)

lemma bin_nth_numeral_unfold:
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral (num.Bit0 x)) n \<longleftrightarrow> n > 0 \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral x) (n - 1)"
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral (num.Bit1 x)) n \<longleftrightarrow> (n > 0 \<longrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral x) (n - 1))"
  by (cases n; simp)+

lemma bintrunc_mod2p: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w = w mod 2 ^ n"
  by (fact take_bit_eq_mod)

lemma sbintrunc_mod2p: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w = (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n"
  by (simp add: bintrunc_mod2p signed_take_bit_eq_take_bit_shift)

lemma sbintrunc_eq_take_bit:
  \<open>(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
  by (fact signed_take_bit_eq_take_bit_shift)

lemma bintrunc_n_0: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n 0 = 0"
  by (fact take_bit_of_0)

lemma sbintrunc_n_0: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n 0 = 0"
  by (fact signed_take_bit_of_0)

lemma sbintrunc_n_minus1: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1) = -1"
  by (fact signed_take_bit_of_minus_1)

lemma bintrunc_Suc_numeral:
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) 1 = 1"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- 1) = 1 + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (numeral (Num.Bit0 w)) = 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- numeral (Num.Bit0 w)) = 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- numeral (w + Num.One))"
  by (simp_all add: take_bit_Suc del: take_bit_minus_one_eq_mask)

lemma sbintrunc_0_numeral [simp]:
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) 0 1 = -1"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) 0 (numeral (Num.Bit0 w)) = 0"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) 0 (numeral (Num.Bit1 w)) = -1"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) 0 (- numeral (Num.Bit0 w)) = 0"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) 0 (- numeral (Num.Bit1 w)) = -1"
  by simp_all

lemma sbintrunc_Suc_numeral:
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) 1 = 1"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (numeral (Num.Bit0 w)) = 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- numeral (Num.Bit0 w)) = 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- numeral (w + Num.One))"
  by (simp_all add: signed_take_bit_Suc)

lemma nth_bintr: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w) n \<longleftrightarrow> n < m \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w n"
  by (fact bit_take_bit_iff)

lemma nth_sbintr: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w) n = (if n < m then (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w n else (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w m)"
  by (simp add: bit_signed_take_bit_iff min_def)

lemma bin_nth_Bit0:
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral w) m)"
  using bit_double_iff [of \<open>numeral w :: int\<close> n]
  by (auto intro: exI [of _ \<open>n - 1\<close>])

lemma bin_nth_Bit1:
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (numeral w) m)"
  using even_bit_succ_iff [of \<open>2 * numeral w :: int\<close> n]
    bit_double_iff [of \<open>numeral w :: int\<close> n]
  by auto

lemma bintrunc_bintrunc_l: "n \<le> m \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by simp

lemma sbintrunc_sbintrunc_l: "n \<le> m \<Longrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by simp

lemma bintrunc_bintrunc_ge: "n \<le> m \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (min m n) w"
  by (rule take_bit_take_bit)

lemma sbintrunc_sbintrunc_min [simp]: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (min m n) w"
  by (rule signed_take_bit_signed_take_bit)

lemmas sbintrunc_Suc_Pls =
  signed_take_bit_Suc [where a="0::int", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Suc_Min =
  signed_take_bit_Suc [where a="-1::int", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Sucs = sbintrunc_Suc_Pls sbintrunc_Suc_Min
  sbintrunc_Suc_numeral

lemmas sbintrunc_Pls =
  signed_take_bit_0 [where a="0::int", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Min =
  signed_take_bit_0 [where a="-1::int", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_0_simps =
  sbintrunc_Pls sbintrunc_Min

lemmas sbintrunc_simps = sbintrunc_0_simps sbintrunc_Sucs

lemma bintrunc_minus: "0 < n \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc (n - 1)) w = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by auto

lemma sbintrunc_minus: "0 < n \<Longrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc (n - 1)) w = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by auto

lemmas sbintrunc_minus_simps =
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans]]

lemma sbintrunc_BIT_I:
  \<open>0 < n \<Longrightarrow>
  (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) 0 = y \<Longrightarrow>
  (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n 0 = 2 * y\<close>
  by simp

lemma sbintrunc_Suc_Is:
  \<open>(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1) = y \<Longrightarrow>
  (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) (- 1) = 1 + 2 * y\<close>
  by auto

lemma sbintrunc_Suc_lem: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) x = y \<Longrightarrow> m = Suc n \<Longrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m x = y"
  by (rule ssubst)

lemmas sbintrunc_Suc_Ialts =
  sbintrunc_Suc_Is [THEN sbintrunc_Suc_lem]

lemma sbintrunc_bintrunc_lt: "m > n \<Longrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w) = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (rule bin_eqI) (auto simp: nth_sbintr nth_bintr)

lemma bintrunc_sbintrunc_le: "m \<le> Suc n \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m w"
  by (rule take_bit_signed_take_bit)

lemmas bintrunc_sbintrunc [simp] = order_refl [THEN bintrunc_sbintrunc_le]
lemmas sbintrunc_bintrunc [simp] = lessI [THEN sbintrunc_bintrunc_lt]
lemmas bintrunc_bintrunc [simp] = order_refl [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc [simp] = order_refl [THEN sbintrunc_sbintrunc_l]

lemma bintrunc_sbintrunc' [simp]: "0 < n \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) w) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (metis Suc_diff_1 bintrunc_sbintrunc)

lemma sbintrunc_bintrunc' [simp]: "0 < n \<Longrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w) = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) w"
  by (simp add: sbintrunc_bintrunc_lt)

lemma bin_sbin_eq_iff: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) x = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) y \<longleftrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y"
  by (simp add: signed_take_bit_eq_iff_take_bit_eq)

lemma bin_sbin_eq_iff':
  "0 < n \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y \<longleftrightarrow> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) x = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) y"
  by (simp add: signed_take_bit_eq_iff_take_bit_eq)

lemmas bintrunc_sbintruncS0 [simp] = bintrunc_sbintrunc' [unfolded One_nat_def]
lemmas sbintrunc_bintruncS0 [simp] = sbintrunc_bintrunc' [unfolded One_nat_def]

lemmas bintrunc_bintrunc_l' = le_add1 [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc_l' = le_add1 [THEN sbintrunc_sbintrunc_l]

(* although bintrunc_minus_simps, if added to default simpset,
  tends to get applied where it's not wanted in developing the theories,
  we get a version for when the word length is given literally *)

lemmas nat_non0_gr =
  trans [OF iszero_def [THEN Not_eq_iff [THEN iffD2]] refl]

lemma bintrunc_numeral:
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) x = of_bool (odd x) + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc take_bit_Suc mod_2_eq_odd)

lemma sbintrunc_numeral:
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) x = of_bool (odd x) + 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_numeral_simps [simp]:
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (numeral (Num.Bit0 w)) =
    2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (- numeral (Num.Bit0 w)) =
    2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (- numeral w)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (- numeral (w + Num.One))"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (numeral (Num.Bit0 w)) =
    2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (- numeral (Num.Bit0 w)) =
    2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (- numeral w)"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (pred_numeral k) (- numeral (w + Num.One))"
  "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n = (\<lambda>w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n) = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (auto simp add: take_bit_eq_mod image_iff) (metis mod_pos_pos_trivial)

lemma no_sbintr_alt2: "signed_take_bit n = (\<lambda>w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp only: signed_take_bit_eq_take_bit_shift flip: take_bit_eq_mod)

lemma range_sbintrunc: "range ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n) = {i. - (2 ^ n) \<le> i \<and> i < 2 ^ n}"
proof -
  have \<open>surj (\<lambda>k::int. k + 2 ^ n)\<close>
    by (rule surjI [of _ \<open>(\<lambda>k. k - 2 ^ n)\<close>]) simp
  moreover have \<open>(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n = ((\<lambda>k. k - 2 ^ n) \<circ> take_bit (Suc n) \<circ> (\<lambda>k. k + 2 ^ n))\<close>
    by (simp add: sbintrunc_eq_take_bit fun_eq_iff)
  ultimately show ?thesis
    apply (simp add: fun.set_map range_bintrunc set_eq_iff image_iff fun_eq_iff)
    by (metis sbintrunc_sbintrunc signed_take_bit_int_eq_self_iff)
qed

lemma sbintrunc_inc:
  \<open>k + 2 ^ Suc n \<le> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n k\<close> if \<open>k < - (2 ^ n)\<close>
  using that by (fact signed_take_bit_int_greater_eq)

lemma sbintrunc_dec:
  \<open>(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n k \<le> k - 2 ^ (Suc n)\<close> if \<open>k \<ge> 2 ^ n\<close>
  using that by (fact signed_take_bit_int_less_eq)

lemma bintr_ge0: "0 \<le> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (simp add: bintrunc_mod2p)

lemma bintr_lt2p: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w < 2 ^ n"
  by (simp add: bintrunc_mod2p)

lemma bintr_Min: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1) = 2 ^ n - 1"
  by (simp add: stable_imp_take_bit_eq mask_eq_exp_minus_1)

lemma sbintr_ge: "- (2 ^ n) \<le> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w"
  by (fact signed_take_bit_int_greater_eq_minus_exp)

lemma sbintr_lt: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w < 2 ^ n"
  by (fact signed_take_bit_int_less_exp)

lemma bin_rest_trunc: "(\<lambda>k::int. k div 2) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - 1) ((\<lambda>k::int. k div 2) bin)"
  by (simp add: take_bit_rec [of n bin])

lemma bin_rest_power_trunc:
  "((\<lambda>k::int. k div 2) ^^ k) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (n - k) (((\<lambda>k::int. k div 2) ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((\<lambda>k::int. k div 2) bin) = (\<lambda>k::int. k div 2) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) bin)"
  by (auto simp add: take_bit_Suc)

lemma bin_rest_strunc: "(\<lambda>k::int. k div 2) ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (Suc n) bin) = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((\<lambda>k::int. k div 2) bin)"
  by (simp add: signed_take_bit_Suc)

lemma bintrunc_rest [simp]: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((\<lambda>k::int. k div 2) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin)) = (\<lambda>k::int. k div 2) ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin)"
  by (induct n arbitrary: bin) (simp_all add: take_bit_Suc)

lemma sbintrunc_rest [simp]: "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((\<lambda>k::int. k div 2) ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin)) = (\<lambda>k::int. k div 2) ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n bin)"
  by (induct n arbitrary: bin) (simp_all add: signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_rest': "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n \<circ> (\<lambda>k::int. k div 2) \<circ> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n = (\<lambda>k::int. k div 2) \<circ> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n"
  by (rule ext) auto

lemma sbintrunc_rest': "(signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n \<circ> (\<lambda>k::int. k div 2) \<circ> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n = (\<lambda>k::int. k div 2) \<circ> (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n"
  by (rule ext) auto

lemma rco_lem:
  assumes "f \<circ> g \<circ> f = g \<circ> f"
  shows "f \<circ> (g \<circ> f) ^^ n = g ^^ n \<circ> f"
proof (induct n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
    by (metis assms comp_assoc funpow_Suc_right)
qed

lemmas rco_bintr = bintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]
lemmas rco_sbintr = sbintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]

context
  includes bit_operations_syntax
begin

lemmas int_not_def = not_int_def

lemma int_not_simps:
  "NOT (0::int) = -1"
  "NOT (1::int) = -2"
  "NOT (- 1::int) = 0"
  "NOT (numeral w::int) = - numeral (w + Num.One)"
  "NOT (- numeral (Num.Bit0 w)::int) = numeral (Num.BitM w)"
  "NOT (- numeral (Num.Bit1 w)::int) = numeral (Num.Bit0 w)"
  by (simp_all add: not_int_def)

lemma int_not_not: "NOT (NOT x) = x"
  for x :: int
  by (fact bit.double_compl)

lemma int_and_0 [simp]: "0 AND x = 0"
  for x :: int
  by (fact bit.conj_zero_left)

lemma int_and_m1 [simp]: "-1 AND x = x"
  for x :: int
  by (fact and.left_neutral)

lemma int_or_zero [simp]: "0 OR x = x"
  for x :: int
  by (fact or.left_neutral)

lemma int_or_minus1 [simp]: "-1 OR x = -1"
  for x :: int
  by (fact bit.disj_one_left)

lemma int_xor_zero [simp]: "0 XOR x = x"
  for x :: int
  by (fact xor.left_neutral)

lemma bin_rest_NOT [simp]: "(\<lambda>k::int. k div 2) (NOT x) = NOT ((\<lambda>k::int. k div 2) x)"
  by (fact not_int_div_2)

lemma bin_last_NOT [simp]: "(odd :: int \<Rightarrow> bool) (NOT x) \<longleftrightarrow> \<not> (odd :: int \<Rightarrow> bool) x"
  by simp

lemma bin_rest_AND [simp]: "(\<lambda>k::int. k div 2) (x AND y) = (\<lambda>k::int. k div 2) x AND (\<lambda>k::int. k div 2) y"
  by (subst and_int_rec) auto

lemma bin_last_AND [simp]: "(odd :: int \<Rightarrow> bool) (x AND y) \<longleftrightarrow> (odd :: int \<Rightarrow> bool) x \<and> (odd :: int \<Rightarrow> bool) y"
  by (subst and_int_rec) auto

lemma bin_rest_OR [simp]: "(\<lambda>k::int. k div 2) (x OR y) = (\<lambda>k::int. k div 2) x OR (\<lambda>k::int. k div 2) y"
  by (subst or_int_rec) auto

lemma bin_last_OR [simp]: "(odd :: int \<Rightarrow> bool) (x OR y) \<longleftrightarrow> (odd :: int \<Rightarrow> bool) x \<or> (odd :: int \<Rightarrow> bool) y"
  by (subst or_int_rec) auto

lemma bin_rest_XOR [simp]: "(\<lambda>k::int. k div 2) (x XOR y) = (\<lambda>k::int. k div 2) x XOR (\<lambda>k::int. k div 2) y"
  by (subst xor_int_rec) auto

lemma bin_last_XOR [simp]: "(odd :: int \<Rightarrow> bool) (x XOR y) \<longleftrightarrow> ((odd :: int \<Rightarrow> bool) x \<or> (odd :: int \<Rightarrow> bool) y) \<and> \<not> ((odd :: int \<Rightarrow> bool) x \<and> (odd :: int \<Rightarrow> bool) y)"
  by (subst xor_int_rec) auto

lemma bin_nth_ops:
  "\<And>x y. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (x AND y) n \<longleftrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n"
  "\<And>x y. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (x OR y) n \<longleftrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n \<or> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n"
  "\<And>x y. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (x XOR y) n \<longleftrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n \<noteq> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) y n"
  "\<And>x. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (NOT x) n \<longleftrightarrow> \<not> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n"
  by (simp_all add: bit_and_iff bit_or_iff bit_xor_iff bit_not_iff)

lemma int_xor_minus1 [simp]: "-1 XOR x = NOT x"
  for x :: int
  by (fact bit.xor_one_left)

lemma int_xor_extra_simps [simp]:
  "w XOR 0 = w"
  "w XOR -1 = NOT w"
  for w :: int
  by simp_all

lemma int_or_extra_simps [simp]:
  "w OR 0 = w"
  "w OR -1 = -1"
  for w :: int
  by simp_all

lemma int_and_extra_simps [simp]:
  "w AND 0 = 0"
  "w AND -1 = w"
  for w :: int
  by simp_all

text \<open>Commutativity of the above.\<close>
lemma bin_ops_comm:
  fixes x y :: int
  shows int_and_comm: "x AND y = y AND x"
    and int_or_comm:  "x OR y = y OR x"
    and int_xor_comm: "x XOR y = y XOR x"
  by (simp_all add: ac_simps)

lemma bin_ops_same [simp]:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: int
  by simp_all

lemmas bin_log_esimps =
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_0 int_and_m1 int_or_zero int_or_minus1 int_xor_zero int_xor_minus1

lemma bbw_ao_absorb: "x AND (y OR x) = x \<and> x OR (y AND x) = x"
  for x y :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = x"
  "(y OR x) AND x = x \<and> x OR (x AND y) = x"
  "(x OR y) AND x = x \<and> (x AND y) OR x = x"
  for x y :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not: "(NOT x) XOR y = NOT (x XOR y) \<and> x XOR (NOT y) = NOT (x XOR y)"
  for x y :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma int_and_assoc: "(x AND y) AND z = x AND (y AND z)"
  for x y z :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma int_or_assoc: "(x OR y) OR z = x OR (y OR z)"
  for x y z :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma int_xor_assoc: "(x XOR y) XOR z = x XOR (y XOR z)"
  for x y z :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]:
  "y AND (x AND z) = x AND (y AND z)"
  "y OR (x OR z) = x OR (y OR z)"
  "y XOR (x XOR z) = x XOR (y XOR z)"
  for x y :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma bbw_not_dist:
  "NOT (x OR y) = (NOT x) AND (NOT y)"
  "NOT (x AND y) = (NOT x) OR (NOT y)"
  for x y :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma bbw_oa_dist: "(x AND y) OR z = (x OR z) AND (y OR z)"
  for x y z :: int
  by (auto simp add: bit_eq_iff bit_simps)

lemma bbw_ao_dist: "(x OR y) AND z = (x AND z) OR (y AND z)"
  for x y z :: int
  by (auto simp add: bit_eq_iff bit_simps)

text \<open>Cases for \<open>0\<close> and \<open>-1\<close> are already covered by other simp rules.\<close>

lemma bin_rest_neg_numeral_BitM [simp]:
  "(\<lambda>k::int. k div 2) (- numeral (Num.BitM w)) = - numeral w"
  by simp

lemma bin_last_neg_numeral_BitM [simp]:
  "(odd :: int \<Rightarrow> bool) (- numeral (Num.BitM w))"
  by simp

text \<open>Interaction between bit-wise and arithmetic: good example of \<open>bin_induction\<close>.\<close>
lemma bin_add_not: "x + NOT x = (-1::int)"
  by (simp add: not_int_def)

lemma AND_mod: "x AND (2 ^ n - 1) = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask mask_eq_exp_minus_1)

lemma bin_trunc_ao:
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x AND (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (x AND y)"
  "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x OR (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (x OR y)"
  by simp_all

lemma bin_trunc_xor: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x XOR (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (x XOR y)"
  by simp

lemma bin_trunc_not: "(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (NOT ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x)) = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (NOT x)"
  by (fact take_bit_not_take_bit)

text \<open>Want theorems of the form of \<open>bin_trunc_xor\<close>.\<close>
lemma bintr_bintr_i: "x = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]

lemma not_int_cmp_0 [simp]:
  fixes i :: int shows
  "0 < NOT i \<longleftrightarrow> i < -1"
  "0 \<le> NOT i \<longleftrightarrow> i < 0"
  "NOT i < 0 \<longleftrightarrow> i \<ge> 0"
  "NOT i \<le> 0 \<longleftrightarrow> i \<ge> -1"
by(simp_all add: int_not_def) arith+

lemma bbw_ao_dist2: "(x :: int) AND (y OR z) = x AND y OR x AND z"
  by (fact bit.conj_disj_distrib)

lemmas int_and_ac = bbw_lcs(1) int_and_comm int_and_assoc

lemma int_nand_same [simp]: fixes x :: int shows "x AND NOT x = 0"
  by simp

lemma int_nand_same_middle: fixes x :: int shows "x AND y AND NOT x = 0"
  by (simp add: bit_eq_iff bit_and_iff bit_not_iff)

lemma and_xor_dist: fixes x :: int shows
  "x AND (y XOR z) = (x AND y) XOR (x AND z)"
  by (fact bit.conj_xor_distrib)

lemma int_and_lt0 [simp]:
  \<open>x AND y < 0 \<longleftrightarrow> x < 0 \<and> y < 0\<close> for x y :: int
  by (fact and_negative_int_iff)

lemma int_and_ge0 [simp]:
  \<open>x AND y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<or> y \<ge> 0\<close> for x y :: int
  by (fact and_nonnegative_int_iff)

lemma int_and_1: fixes x :: int shows "x AND 1 = x mod 2"
  by (fact and_one_eq)

lemma int_1_and: fixes x :: int shows "1 AND x = x mod 2"
  by (fact one_and_eq)

lemma int_or_lt0 [simp]:
  \<open>x OR y < 0 \<longleftrightarrow> x < 0 \<or> y < 0\<close> for x y :: int
  by (fact or_negative_int_iff)

lemma int_or_ge0 [simp]:
  \<open>x OR y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<and> y \<ge> 0\<close> for x y :: int
  by (fact or_nonnegative_int_iff)

lemma int_xor_lt0 [simp]:
  \<open>x XOR y < 0 \<longleftrightarrow> (x < 0) \<noteq> (y < 0)\<close> for x y :: int
  by (fact xor_negative_int_iff)

lemma int_xor_ge0 [simp]:
  \<open>x XOR y \<ge> 0 \<longleftrightarrow> (x \<ge> 0 \<longleftrightarrow> y \<ge> 0)\<close> for x y :: int
  by (fact xor_nonnegative_int_iff)

lemma even_conv_AND:
  \<open>even i \<longleftrightarrow> i AND 1 = 0\<close> for i :: int
  by (simp add: and_one_eq mod2_eq_if)

lemma bin_last_conv_AND:
  "(odd :: int \<Rightarrow> bool) i \<longleftrightarrow> i AND 1 \<noteq> 0"
  by (simp add: and_one_eq mod2_eq_if)

lemma bitval_bin_last:
  "of_bool ((odd :: int \<Rightarrow> bool) i) = i AND 1"
  by (simp add: and_one_eq mod2_eq_if)

lemma int_not_neg_numeral: "NOT (- numeral n) = (Num.sub n num.One :: int)"
by(simp add: int_not_def)

lemma int_neg_numeral_pOne_conv_not: "- numeral (n + num.One) = (NOT (numeral n) :: int)"
by(simp add: int_not_def)

lemma int_0_shiftl: "push_bit n 0 = (0 :: int)"
  by (fact push_bit_of_0)

lemma bin_last_shiftl: "odd (push_bit n x) \<longleftrightarrow> n = 0 \<and> (odd :: int \<Rightarrow> bool) x"
  by simp

lemma bin_rest_shiftl: "(\<lambda>k::int. k div 2) (push_bit n x) = (if n > 0 then push_bit (n - 1) x else (\<lambda>k::int. k div 2) x)"
  by (cases n) (simp_all add: push_bit_eq_mult)

lemma bin_nth_shiftl: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (push_bit n x) m \<longleftrightarrow> n \<le> m \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x (m - n)"
  by (fact bit_push_bit_iff_int)

lemma bin_last_shiftr: "odd (drop_bit n x) \<longleftrightarrow> bit x n" for x :: int
  by (simp add: bit_iff_odd_drop_bit)

lemma bin_rest_shiftr: "(\<lambda>k::int. k div 2) (drop_bit n x) = drop_bit (Suc n) x"
  by (simp add: drop_bit_Suc drop_bit_half)

lemma bin_nth_shiftr: "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) (drop_bit n x) m = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) x (n + m)"
  by (simp add: bit_simps)

lemma bin_nth_conv_AND:
  fixes x :: int shows
  "(bit :: int \<Rightarrow> nat \<Rightarrow> bool) x n \<longleftrightarrow> x AND (push_bit n 1) \<noteq> 0"
  by (fact bit_iff_and_push_bit_not_eq_0)

lemma int_shiftl_numeral [simp]:
  "push_bit (numeral w') (numeral w :: int) = push_bit (pred_numeral w') (numeral (num.Bit0 w))"
  "push_bit (numeral w') (- numeral w :: int) = push_bit (pred_numeral w') (- numeral (num.Bit0 w))"
  by (fact push_bit_numeral push_bit_minus_numeral)+

lemma int_shiftl_One_numeral [simp]:
  "push_bit (numeral w) (1::int) = push_bit (pred_numeral w) 2"
  using int_shiftl_numeral [of Num.One w]
  by (simp only: numeral_eq_Suc push_bit_Suc) simp

lemma shiftl_ge_0: fixes i :: int shows "push_bit n i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by (fact push_bit_nonnegative_int_iff)

lemma shiftl_lt_0: fixes i :: int shows "push_bit n i < 0 \<longleftrightarrow> i < 0"
  by (fact push_bit_negative_int_iff)

lemma int_shiftl_test_bit: "bit (push_bit i n :: int) m \<longleftrightarrow> m \<ge> i \<and> bit n (m - i)"
  by (fact bit_push_bit_iff_int)

lemma int_0shiftr: "drop_bit x (0 :: int) = 0"
  by (fact drop_bit_of_0)

lemma int_minus1_shiftr: "drop_bit x (-1 :: int) = -1"
  by (fact drop_bit_minus_one)

lemma int_shiftr_ge_0: fixes i :: int shows "drop_bit n i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by (fact drop_bit_nonnegative_int_iff)

lemma int_shiftr_lt_0 [simp]: fixes i :: int shows "drop_bit n i < 0 \<longleftrightarrow> i < 0"
  by (fact drop_bit_negative_int_iff)

lemma int_shiftr_numeral [simp]:
  "drop_bit (numeral w') (1 :: int) = 0"
  "drop_bit (numeral w') (numeral num.One :: int) = 0"
  "drop_bit (numeral w') (numeral (num.Bit0 w) :: int) = drop_bit (pred_numeral w') (numeral w)"
  "drop_bit (numeral w') (numeral (num.Bit1 w) :: int) = drop_bit (pred_numeral w') (numeral w)"
  "drop_bit (numeral w') (- numeral (num.Bit0 w) :: int) = drop_bit (pred_numeral w') (- numeral w)"
  "drop_bit (numeral w') (- numeral (num.Bit1 w) :: int) = drop_bit (pred_numeral w') (- numeral (Num.inc w))"
  by (simp_all add: numeral_eq_Suc add_One drop_bit_Suc)

lemma int_shiftr_numeral_Suc0 [simp]:
  "drop_bit (Suc 0) (1 :: int) = 0"
  "drop_bit (Suc 0) (numeral num.One :: int) = 0"
  "drop_bit (Suc 0) (numeral (num.Bit0 w) :: int) = numeral w"
  "drop_bit (Suc 0) (numeral (num.Bit1 w) :: int) = numeral w"
  "drop_bit (Suc 0) (- numeral (num.Bit0 w) :: int) = - numeral w"
  "drop_bit (Suc 0) (- numeral (num.Bit1 w) :: int) = - numeral (Num.inc w)"
  by (simp_all add: drop_bit_Suc add_One)

lemmas bin_log_bintrs = bin_trunc_not bin_trunc_xor bin_trunc_and bin_trunc_or

lemma bintrunc_shiftl:
  "take_bit n (push_bit i m) = push_bit i (take_bit (n - i) m)"
  for m :: int
  by (fact take_bit_push_bit)

lemma bin_mask_conv_pow2:
  "mask n = 2 ^ n - (1 :: int)"
  by (fact mask_eq_exp_minus_1)

lemma bin_mask_ge0: "mask n \<ge> (0 :: int)"
  by (fact mask_nonnegative_int)

context
  includes bit_operations_syntax
begin

lemma and_bin_mask_conv_mod: "x AND mask n = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask)

end

end

lemma bin_mask_numeral:
  "mask (numeral n) = (1 :: int) + 2 * mask (pred_numeral n)"
  by (fact mask_numeral)

lemma bin_nth_mask: "bit (mask n :: int) i \<longleftrightarrow> i < n"
  by (simp add: bit_mask_iff)

lemma bin_mask_p1_conv_shift: "mask n + 1 = push_bit n (1 :: int)"
  by (simp add: inc_mask_eq_exp)

lemma sbintrunc_eq_in_range:
  "((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x = x) = (x \<in> range ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n))"
  "(x = (signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n x) = (x \<in> range ((signed_take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n))"
  by (simp add: image_def, metis sbintrunc_sbintrunc)+

lemma sbintrunc_If:
  "- 3 * (2 ^ n) \<le> x \<and> x < 3 * (2 ^ n)
    \<Longrightarrow> signed_take_bit n x = (if x < - (2 ^ n) then x + 2 * (2 ^ n)
        else if x \<ge> 2 ^ n then x - 2 * (2 ^ n) else x)" for x :: int
  apply (simp add: no_sbintr_alt2)
  by (smt (verit, best) minus_mod_self2 mod_add_self2 mod_pos_pos_trivial)


lemma bintrunc_id:
  "\<lbrakk>m \<le> int n; 0 < m\<rbrakk> \<Longrightarrow> take_bit n m = m"
  by (simp add: take_bit_int_eq_self_iff le_less_trans)

end
