(*
 * Copyright Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Bitwise Operations on integers\<close>

theory Bits_Int
  imports
    "HOL-Library.Word"
    Traditional_Infix_Syntax
begin

subsection \<open>Implicit bit representation of \<^typ>\<open>int\<close>\<close>

abbreviation (input) bin_last :: "int \<Rightarrow> bool"
  where "bin_last \<equiv> odd"

lemma bin_last_def:
  "bin_last w \<longleftrightarrow> w mod 2 = 1"
  by (fact odd_iff_mod_2_eq_one)

abbreviation (input) bin_rest :: "int \<Rightarrow> int"
  where "bin_rest w \<equiv> w div 2"

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
  "bin_rest 0 = 0"
  "bin_rest 1 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest Numeral1 = 0"
  "bin_rest (numeral (Num.Bit0 w)) = numeral w"
  "bin_rest (numeral (Num.Bit1 w)) = numeral w"
  "bin_rest (- numeral (Num.Bit0 w)) = - numeral w"
  "bin_rest (- numeral (Num.Bit1 w)) = - numeral (w + Num.One)"
  by simp_all

lemma bin_rl_eqI: "\<lbrakk>bin_rest x = bin_rest y; odd x = odd y\<rbrakk> \<Longrightarrow> x = y"
  by (auto elim: oddE)

lemma [simp]:
  shows bin_rest_lt0: "bin_rest i < 0 \<longleftrightarrow> i < 0"
  and  bin_rest_ge_0: "bin_rest i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by auto

lemma bin_rest_gt_0 [simp]: "bin_rest x > 0 \<longleftrightarrow> x > 1"
  by auto


subsection \<open>Bit projection\<close>

abbreviation (input) bin_nth :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bin_nth \<equiv> bit\<close>

lemma bin_nth_eq_iff: "bin_nth x = bin_nth y \<longleftrightarrow> x = y"
  by (simp add: bit_eq_iff fun_eq_iff)

lemma bin_eqI:
  "x = y" if "\<And>n. bin_nth x n \<longleftrightarrow> bin_nth y n"
  using that bin_nth_eq_iff [of x y] by (simp add: fun_eq_iff)

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
  by (fact bit_eq_iff)

lemma bin_nth_zero [simp]: "\<not> bin_nth 0 n"
  by simp

lemma bin_nth_1 [simp]: "bin_nth 1 n \<longleftrightarrow> n = 0"
  by (cases n) (simp_all add: bit_Suc)

lemma bin_nth_minus1 [simp]: "bin_nth (- 1) n"
  by (induction n) (simp_all add: bit_Suc)

lemma bin_nth_numeral: "bin_rest x = y \<Longrightarrow> bin_nth x (numeral n) = bin_nth y (pred_numeral n)"
  by (simp add: numeral_eq_Suc bit_Suc)

lemmas bin_nth_numeral_simps [simp] =
  bin_nth_numeral [OF bin_rest_numeral_simps(8)]

lemmas bin_nth_simps =
  bit_0 bit_Suc bin_nth_zero bin_nth_minus1
  bin_nth_numeral_simps

lemma nth_2p_bin: "bin_nth (2 ^ n) m = (m = n)" \<comment> \<open>for use when simplifying with \<open>bin_nth_Bit\<close>\<close>
  by (auto simp add: bit_exp_iff)

lemma nth_rest_power_bin: "bin_nth ((bin_rest ^^ k) w) n = bin_nth w (n + k)"
  apply (induct k arbitrary: n)
   apply clarsimp
  apply clarsimp
  apply (simp only: bit_Suc [symmetric] add_Suc)
  done

lemma bin_nth_numeral_unfold:
  "bin_nth (numeral (num.Bit0 x)) n \<longleftrightarrow> n > 0 \<and> bin_nth (numeral x) (n - 1)"
  "bin_nth (numeral (num.Bit1 x)) n \<longleftrightarrow> (n > 0 \<longrightarrow> bin_nth (numeral x) (n - 1))"
  by (cases n; simp)+


subsection \<open>Truncating\<close>

definition bin_sign :: "int \<Rightarrow> int"
  where "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (- 1) = - 1"
  "bin_sign (numeral k) = 0"
  "bin_sign (- numeral k) = -1"
  by (simp_all add: bin_sign_def)

lemma bin_sign_rest [simp]: "bin_sign (bin_rest w) = bin_sign w"
  by (simp add: bin_sign_def)

abbreviation (input) bintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bintrunc \<equiv> take_bit\<close>

lemma bintrunc_mod2p: "bintrunc n w = w mod 2 ^ n"
  by (fact take_bit_eq_mod)

abbreviation (input) sbintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>sbintrunc \<equiv> signed_take_bit\<close>

abbreviation (input) norm_sint :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>norm_sint n \<equiv> signed_take_bit (n - 1)\<close>

lemma sbintrunc_mod2p: "sbintrunc n w = (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n"
  by (simp add: bintrunc_mod2p signed_take_bit_eq_take_bit_shift)

lemma sbintrunc_eq_take_bit:
  \<open>sbintrunc n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
  by (fact signed_take_bit_eq_take_bit_shift)

lemma sign_bintr: "bin_sign (bintrunc n w) = 0"
  by (simp add: bin_sign_def)

lemma bintrunc_n_0: "bintrunc n 0 = 0"
  by (fact take_bit_of_0)

lemma sbintrunc_n_0: "sbintrunc n 0 = 0"
  by (fact signed_take_bit_of_0)

lemma sbintrunc_n_minus1: "sbintrunc n (- 1) = -1"
  by (fact signed_take_bit_of_minus_1)

lemma bintrunc_Suc_numeral:
  "bintrunc (Suc n) 1 = 1"
  "bintrunc (Suc n) (- 1) = 1 + 2 * bintrunc n (- 1)"
  "bintrunc (Suc n) (numeral (Num.Bit0 w)) = 2 * bintrunc n (numeral w)"
  "bintrunc (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * bintrunc n (numeral w)"
  "bintrunc (Suc n) (- numeral (Num.Bit0 w)) = 2 * bintrunc n (- numeral w)"
  "bintrunc (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * bintrunc n (- numeral (w + Num.One))"
  by (simp_all add: take_bit_Suc)

lemma sbintrunc_0_numeral [simp]:
  "sbintrunc 0 1 = -1"
  "sbintrunc 0 (numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (numeral (Num.Bit1 w)) = -1"
  "sbintrunc 0 (- numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (- numeral (Num.Bit1 w)) = -1"
  by simp_all

lemma sbintrunc_Suc_numeral:
  "sbintrunc (Suc n) 1 = 1"
  "sbintrunc (Suc n) (numeral (Num.Bit0 w)) = 2 * sbintrunc n (numeral w)"
  "sbintrunc (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * sbintrunc n (numeral w)"
  "sbintrunc (Suc n) (- numeral (Num.Bit0 w)) = 2 * sbintrunc n (- numeral w)"
  "sbintrunc (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * sbintrunc n (- numeral (w + Num.One))"
  by (simp_all add: signed_take_bit_Suc)

lemma bin_sign_lem: "(bin_sign (sbintrunc n bin) = -1) = bit bin n"
  by (simp add: bin_sign_def)

lemma nth_bintr: "bin_nth (bintrunc m w) n \<longleftrightarrow> n < m \<and> bin_nth w n"
  by (fact bit_take_bit_iff)

lemma nth_sbintr: "bin_nth (sbintrunc m w) n = (if n < m then bin_nth w n else bin_nth w m)"
  by (simp add: bit_signed_take_bit_iff min_def)

lemma bin_nth_Bit0:
  "bin_nth (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bit_double_iff [of \<open>numeral w :: int\<close> n]
  by (auto intro: exI [of _ \<open>n - 1\<close>])

lemma bin_nth_Bit1:
  "bin_nth (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using even_bit_succ_iff [of \<open>2 * numeral w :: int\<close> n]
    bit_double_iff [of \<open>numeral w :: int\<close> n]
  by auto

lemma bintrunc_bintrunc_l: "n \<le> m \<Longrightarrow> bintrunc m (bintrunc n w) = bintrunc n w"
  by simp

lemma sbintrunc_sbintrunc_l: "n \<le> m \<Longrightarrow> sbintrunc m (sbintrunc n w) = sbintrunc n w"
  by (simp add: min_def)

lemma bintrunc_bintrunc_ge: "n \<le> m \<Longrightarrow> bintrunc n (bintrunc m w) = bintrunc n w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]: "bintrunc m (bintrunc n w) = bintrunc (min m n) w"
  by (rule take_bit_take_bit)

lemma sbintrunc_sbintrunc_min [simp]: "sbintrunc m (sbintrunc n w) = sbintrunc (min m n) w"
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

lemma bintrunc_minus: "0 < n \<Longrightarrow> bintrunc (Suc (n - 1)) w = bintrunc n w"
  by auto

lemma sbintrunc_minus: "0 < n \<Longrightarrow> sbintrunc (Suc (n - 1)) w = sbintrunc n w"
  by auto

lemmas sbintrunc_minus_simps =
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans]]

lemma sbintrunc_BIT_I:
  \<open>0 < n \<Longrightarrow>
  sbintrunc (n - 1) 0 = y \<Longrightarrow>
  sbintrunc n 0 = 2 * y\<close>
  by simp

lemma sbintrunc_Suc_Is:
  \<open>sbintrunc n (- 1) = y \<Longrightarrow>
  sbintrunc (Suc n) (- 1) = 1 + 2 * y\<close>
  by auto

lemma sbintrunc_Suc_lem: "sbintrunc (Suc n) x = y \<Longrightarrow> m = Suc n \<Longrightarrow> sbintrunc m x = y"
  by (rule ssubst)

lemmas sbintrunc_Suc_Ialts =
  sbintrunc_Suc_Is [THEN sbintrunc_Suc_lem]

lemma sbintrunc_bintrunc_lt: "m > n \<Longrightarrow> sbintrunc n (bintrunc m w) = sbintrunc n w"
  by (rule bin_eqI) (auto simp: nth_sbintr nth_bintr)

lemma bintrunc_sbintrunc_le: "m \<le> Suc n \<Longrightarrow> bintrunc m (sbintrunc n w) = bintrunc m w"
  by (rule take_bit_signed_take_bit)

lemmas bintrunc_sbintrunc [simp] = order_refl [THEN bintrunc_sbintrunc_le]
lemmas sbintrunc_bintrunc [simp] = lessI [THEN sbintrunc_bintrunc_lt]
lemmas bintrunc_bintrunc [simp] = order_refl [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc [simp] = order_refl [THEN sbintrunc_sbintrunc_l]

lemma bintrunc_sbintrunc' [simp]: "0 < n \<Longrightarrow> bintrunc n (sbintrunc (n - 1) w) = bintrunc n w"
  by (cases n) simp_all

lemma sbintrunc_bintrunc' [simp]: "0 < n \<Longrightarrow> sbintrunc (n - 1) (bintrunc n w) = sbintrunc (n - 1) w"
  by (cases n) simp_all

lemma bin_sbin_eq_iff: "bintrunc (Suc n) x = bintrunc (Suc n) y \<longleftrightarrow> sbintrunc n x = sbintrunc n y"
  apply (rule iffI)
   apply (rule box_equals [OF _ sbintrunc_bintrunc sbintrunc_bintrunc])
   apply simp
  apply (rule box_equals [OF _ bintrunc_sbintrunc bintrunc_sbintrunc])
  apply simp
  done

lemma bin_sbin_eq_iff':
  "0 < n \<Longrightarrow> bintrunc n x = bintrunc n y \<longleftrightarrow> sbintrunc (n - 1) x = sbintrunc (n - 1) y"
  by (cases n) (simp_all add: bin_sbin_eq_iff)

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
  "bintrunc (numeral k) x = of_bool (odd x) + 2 * bintrunc (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc take_bit_Suc mod_2_eq_odd)

lemma sbintrunc_numeral:
  "sbintrunc (numeral k) x = of_bool (odd x) + 2 * sbintrunc (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_numeral_simps [simp]:
  "bintrunc (numeral k) (numeral (Num.Bit0 w)) =
    2 * bintrunc (pred_numeral k) (numeral w)"
  "bintrunc (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * bintrunc (pred_numeral k) (numeral w)"
  "bintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    2 * bintrunc (pred_numeral k) (- numeral w)"
  "bintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * bintrunc (pred_numeral k) (- numeral (w + Num.One))"
  "bintrunc (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "sbintrunc (numeral k) (numeral (Num.Bit0 w)) =
    2 * sbintrunc (pred_numeral k) (numeral w)"
  "sbintrunc (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * sbintrunc (pred_numeral k) (numeral w)"
  "sbintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    2 * sbintrunc (pred_numeral k) (- numeral w)"
  "sbintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * sbintrunc (pred_numeral k) (- numeral (w + Num.One))"
  "sbintrunc (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "bintrunc n = (\<lambda>w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range (bintrunc n) = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (auto simp add: take_bit_eq_mod image_iff) (metis mod_pos_pos_trivial)

lemma no_sbintr_alt2: "sbintrunc n = (\<lambda>w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp add : sbintrunc_mod2p)

lemma range_sbintrunc: "range (sbintrunc n) = {i. - (2 ^ n) \<le> i \<and> i < 2 ^ n}"
proof -
  have \<open>surj (\<lambda>k::int. k + 2 ^ n)\<close>
    by (rule surjI [of _ \<open>(\<lambda>k. k - 2 ^ n)\<close>]) simp
  moreover have \<open>sbintrunc n = ((\<lambda>k. k - 2 ^ n) \<circ> take_bit (Suc n) \<circ> (\<lambda>k. k + 2 ^ n))\<close>
    by (simp add: sbintrunc_eq_take_bit fun_eq_iff)
  ultimately show ?thesis
    apply (simp only: fun.set_map range_bintrunc)
    apply (auto simp add: image_iff)
    apply presburger
    done
qed

lemma sbintrunc_inc:
  \<open>k + 2 ^ Suc n \<le> sbintrunc n k\<close> if \<open>k < - (2 ^ n)\<close>
  using that by (fact signed_take_bit_int_greater_eq)

lemma sbintrunc_dec:
  \<open>sbintrunc n k \<le> k - 2 ^ (Suc n)\<close> if \<open>k \<ge> 2 ^ n\<close>
  using that by (fact signed_take_bit_int_less_eq)

lemma bintr_ge0: "0 \<le> bintrunc n w"
  by (simp add: bintrunc_mod2p)

lemma bintr_lt2p: "bintrunc n w < 2 ^ n"
  by (simp add: bintrunc_mod2p)

lemma bintr_Min: "bintrunc n (- 1) = 2 ^ n - 1"
  by (simp add: stable_imp_take_bit_eq)

lemma sbintr_ge: "- (2 ^ n) \<le> sbintrunc n w"
  by (simp add: sbintrunc_mod2p)

lemma sbintr_lt: "sbintrunc n w < 2 ^ n"
  by (simp add: sbintrunc_mod2p)

lemma sign_Pls_ge_0: "bin_sign bin = 0 \<longleftrightarrow> bin \<ge> 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma sign_Min_lt_0: "bin_sign bin = -1 \<longleftrightarrow> bin < 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma bin_rest_trunc: "bin_rest (bintrunc n bin) = bintrunc (n - 1) (bin_rest bin)"
  by (simp add: take_bit_rec [of n bin])

lemma bin_rest_power_trunc:
  "(bin_rest ^^ k) (bintrunc n bin) = bintrunc (n - k) ((bin_rest ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i: "bintrunc n (bin_rest bin) = bin_rest (bintrunc (Suc n) bin)"
  by (auto simp add: take_bit_Suc)

lemma bin_rest_strunc: "bin_rest (sbintrunc (Suc n) bin) = sbintrunc n (bin_rest bin)"
  by (simp add: signed_take_bit_Suc)

lemma bintrunc_rest [simp]: "bintrunc n (bin_rest (bintrunc n bin)) = bin_rest (bintrunc n bin)"
  by (induct n arbitrary: bin) (simp_all add: take_bit_Suc)

lemma sbintrunc_rest [simp]: "sbintrunc n (bin_rest (sbintrunc n bin)) = bin_rest (sbintrunc n bin)"
  by (induct n arbitrary: bin) (simp_all add: signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_rest': "bintrunc n \<circ> bin_rest \<circ> bintrunc n = bin_rest \<circ> bintrunc n"
  by (rule ext) auto

lemma sbintrunc_rest': "sbintrunc n \<circ> bin_rest \<circ> sbintrunc n = bin_rest \<circ> sbintrunc n"
  by (rule ext) auto

lemma rco_lem: "f \<circ> g \<circ> f = g \<circ> f \<Longrightarrow> f \<circ> (g \<circ> f) ^^ n = g ^^ n \<circ> f"
  apply (rule ext)
  apply (induct_tac n)
   apply (simp_all (no_asm))
  apply (drule fun_cong)
  apply (unfold o_def)
  apply (erule trans)
  apply simp
  done

lemmas rco_bintr = bintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]
lemmas rco_sbintr = sbintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]


subsection \<open>Splitting and concatenation\<close>

definition bin_split :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<times> int\<close>
  where [simp]: \<open>bin_split n k = (drop_bit n k, take_bit n k)\<close>

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (w div 2) in (w1, of_bool (odd w) + 2 * w2))"
  "bin_split 0 w = (w, 0)"
  by (simp_all add: drop_bit_Suc take_bit_Suc mod_2_eq_odd)

abbreviation (input) bin_cat :: \<open>int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bin_cat k n l \<equiv> concat_bit n l k\<close>

lemma bin_cat_eq_push_bit_add_take_bit:
  \<open>bin_cat k n l = push_bit n k + take_bit n l\<close>
  by (simp add: concat_bit_eq)

lemma bin_sign_cat: "bin_sign (bin_cat x n y) = bin_sign x"
proof -
  have \<open>0 \<le> x\<close> if \<open>0 \<le> x * 2 ^ n + y mod 2 ^ n\<close>
  proof -
    have \<open>y mod 2 ^ n < 2 ^ n\<close>
      using pos_mod_bound [of \<open>2 ^ n\<close> y] by simp
    then have \<open>\<not> y mod 2 ^ n \<ge> 2 ^ n\<close>
      by (simp add: less_le)
    with that have \<open>x \<noteq> - 1\<close>
      by auto
    have *: \<open>- 1 \<le> (- (y mod 2 ^ n)) div 2 ^ n\<close>
      by (simp add: zdiv_zminus1_eq_if)
    from that have \<open>- (y mod 2 ^ n) \<le> x * 2 ^ n\<close>
      by simp
    then have \<open>(- (y mod 2 ^ n)) div 2 ^ n \<le> (x * 2 ^ n) div 2 ^ n\<close>
      using zdiv_mono1 zero_less_numeral zero_less_power by blast
    with * have \<open>- 1 \<le> x * 2 ^ n div 2 ^ n\<close> by simp
    with \<open>x \<noteq> - 1\<close> show ?thesis
      by simp
  qed
  then show ?thesis
    by (simp add: bin_sign_def not_le not_less bin_cat_eq_push_bit_add_take_bit push_bit_eq_mult take_bit_eq_mod)
qed

lemma bin_cat_assoc: "bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)"
  by (fact concat_bit_assoc)

lemma bin_cat_assoc_sym: "bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  by (fact concat_bit_assoc_sym)

definition bin_rcat :: \<open>nat \<Rightarrow> int list \<Rightarrow> int\<close>
  where \<open>bin_rcat n = horner_sum (take_bit n) (2 ^ n) \<circ> rev\<close>

lemma bin_rcat_eq_foldl:
  \<open>bin_rcat n = foldl (\<lambda>u v. bin_cat u n v) 0\<close>
proof
  fix ks :: \<open>int list\<close>
  show \<open>bin_rcat n ks = foldl (\<lambda>u v. bin_cat u n v) 0 ks\<close>
    by (induction ks rule: rev_induct)
      (simp_all add: bin_rcat_def concat_bit_eq push_bit_eq_mult)
qed

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split n c
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

value \<open>bin_rsplit 1705 (3, 88)\<close>

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplitl_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split (min m n) c
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_nth_cat:
  "bin_nth (bin_cat x k y) n =
    (if n < k then bin_nth y n else bin_nth x (n - k))"
  by (simp add: bit_concat_bit_iff)

lemma bin_nth_drop_bit_iff:
  \<open>bin_nth (drop_bit n c) k \<longleftrightarrow> bin_nth c (n + k)\<close>
  by (simp add: bit_drop_bit_eq)

lemma bin_nth_take_bit_iff:
  \<open>bin_nth (take_bit n c) k \<longleftrightarrow> k < n \<and> bin_nth c k\<close>
  by (fact bit_take_bit_iff)

lemma bin_nth_split:
  "bin_split n c = (a, b) \<Longrightarrow>
    (\<forall>k. bin_nth a k = bin_nth c (n + k)) \<and>
    (\<forall>k. bin_nth b k = (k < n \<and> bin_nth c k))"
  by (auto simp add: bin_nth_drop_bit_iff bin_nth_take_bit_iff)

lemma bin_cat_zero [simp]: "bin_cat 0 n w = bintrunc n w"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma bintr_cat1: "bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (metis bin_cat_assoc bin_cat_zero)

lemma bintr_cat: "bintrunc m (bin_cat a n b) =
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"

  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)

lemma bintr_cat_same [simp]: "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: "bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma split_bintrunc: "bin_split n c = (a, b) \<Longrightarrow> b = bintrunc n c"
  by simp

lemma bin_cat_split: "bin_split n w = (u, v) \<Longrightarrow> w = bin_cat u n v"
  by (auto simp add: bin_cat_eq_push_bit_add_take_bit bits_ident)

lemma drop_bit_bin_cat_eq:
  \<open>drop_bit n (bin_cat v n w) = v\<close>
  by (rule bit_eqI) (simp add: bit_drop_bit_eq bit_concat_bit_iff)

lemma take_bit_bin_cat_eq:
  \<open>take_bit n (bin_cat v n w) = take_bit n w\<close>
  by (rule bit_eqI) (simp add: bit_concat_bit_iff)

lemma bin_split_cat: "bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (simp add: drop_bit_bin_cat_eq take_bit_bin_cat_eq)

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by simp

lemma bin_split_minus1 [simp]:
  "bin_split n (- 1) = (- 1, bintrunc n (- 1))"
  by simp

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def drop_bit_Suc take_bit_Suc mod_2_eq_odd split: prod.split_asm)
  done

lemma bin_split_trunc1:
  "bin_split n c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def drop_bit_Suc take_bit_Suc mod_2_eq_odd split: prod.split_asm)
  done

lemma bin_cat_num: "bin_cat a n b = a * 2 ^ n + bintrunc n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit push_bit_eq_mult)

lemma bin_split_num: "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  by (simp add: drop_bit_eq_div take_bit_eq_mod)

lemmas bin_rsplit_aux_simps = bin_rsplit_aux.simps bin_rsplitl_aux.simps
lemmas rsplit_aux_simps = bin_rsplit_aux_simps

lemmas th_if_simp1 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct1, THEN mp] for l
lemmas th_if_simp2 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct2, THEN mp] for l

lemmas rsplit_aux_simp1s = rsplit_aux_simps [THEN th_if_simp1]

lemmas rsplit_aux_simp2ls = rsplit_aux_simps [THEN th_if_simp2]
\<comment> \<open>these safe to \<open>[simp add]\<close> as require calculating \<open>m - n\<close>\<close>
lemmas bin_rsplit_aux_simp2s [simp] = rsplit_aux_simp2ls [unfolded Let_def]
lemmas rbscl = bin_rsplit_aux_simp2s (2)

lemmas rsplit_aux_0_simps [simp] =
  rsplit_aux_simp1s [OF disjI1] rsplit_aux_simp1s [OF disjI2]

lemma bin_rsplit_aux_append: "bin_rsplit_aux n m c (bs @ cs) = bin_rsplit_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemma bin_rsplitl_aux_append: "bin_rsplitl_aux n m c (bs @ cs) = bin_rsplitl_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplitl_aux.induct)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplitl_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemmas rsplit_aux_apps [where bs = "[]"] =
  bin_rsplit_aux_append bin_rsplitl_aux_append

lemmas rsplit_def_auxs = bin_rsplit_def bin_rsplitl_def

lemmas rsplit_aux_alts = rsplit_aux_apps
  [unfolded append_Nil rsplit_def_auxs [symmetric]]

lemma bin_split_minus: "0 < n \<Longrightarrow> bin_split (Suc (n - 1)) w = bin_split n w"
  by auto

lemma bin_split_pred_simp [simp]:
  "(0::nat) < numeral bin \<Longrightarrow>
    bin_split (numeral bin) w =
      (let (w1, w2) = bin_split (numeral bin - 1) (bin_rest w)
       in (w1, of_bool (odd w) + 2 * w2))"
  by (simp add: take_bit_rec drop_bit_rec mod_2_eq_odd)

lemma bin_rsplit_aux_simp_alt:
  "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else let (a, b) = bin_split n c in bin_rsplit n (m - n, a) @ b # bs)"
  apply (simp add: bin_rsplit_aux.simps [of n m c bs])
  apply (subst rsplit_aux_alts)
  apply (simp add: bin_rsplit_def)
  done

lemmas bin_rsplit_simp_alt =
  trans [OF bin_rsplit_def bin_rsplit_aux_simp_alt]

lemmas bthrs = bin_rsplit_simp_alt [THEN [2] trans]

lemma bin_rsplit_size_sign' [rule_format]:
  "n > 0 \<Longrightarrow> rev sw = bin_rsplit n (nw, w) \<Longrightarrow> \<forall>v\<in>set sw. bintrunc n v = v"
  apply (induct sw arbitrary: nw w)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply clarify
  apply simp
  done

lemmas bin_rsplit_size_sign = bin_rsplit_size_sign' [OF asm_rl
  rev_rev_ident [THEN trans] set_rev [THEN equalityD2 [THEN subsetD]]]

lemma bin_nth_rsplit [rule_format] :
  "n > 0 \<Longrightarrow> m < n \<Longrightarrow>
    \<forall>w k nw.
      rev sw = bin_rsplit n (nw, w) \<longrightarrow>
      k < size sw \<longrightarrow> bin_nth (sw ! k) m = bin_nth w (k * n + m)"
  apply (induct sw)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply (erule allE, erule impE, erule exI)
  apply (case_tac k)
   apply clarsimp
   prefer 2
   apply clarsimp
   apply (erule allE)
   apply (erule (1) impE)
   apply (simp add: bit_drop_bit_eq ac_simps)
  apply (simp add: bit_take_bit_iff ac_simps)
  done

lemma bin_rsplit_all: "0 < nw \<Longrightarrow> nw \<le> n \<Longrightarrow> bin_rsplit n (nw, w) = [bintrunc n w]"
  by (auto simp: bin_rsplit_def rsplit_aux_simp2ls split: prod.split dest!: split_bintrunc)

lemma bin_rsplit_l [rule_format]:
  "\<forall>bin. bin_rsplitl n (m, bin) = bin_rsplit n (m, bintrunc m bin)"
  apply (rule_tac a = "m" in wf_less_than [THEN wf_induct])
  apply (simp (no_asm) add: bin_rsplitl_def bin_rsplit_def)
  apply (rule allI)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (simp add: ac_simps)
  apply (subst rsplit_aux_alts(1))
  apply (subst rsplit_aux_alts(2))
  apply clarsimp
  unfolding bin_rsplit_def bin_rsplitl_def
  apply (simp add: drop_bit_take_bit)
  apply (case_tac \<open>x < n\<close>)
  apply (simp_all add: not_less min_def)
  done

lemma bin_rsplit_rcat [rule_format]:
  "n > 0 \<longrightarrow> bin_rsplit n (n * size ws, bin_rcat n ws) = map (bintrunc n) ws"
  apply (unfold bin_rsplit_def bin_rcat_eq_foldl)
  apply (rule_tac xs = ws in rev_induct)
   apply clarsimp
  apply clarsimp
  apply (subst rsplit_aux_alts)
  apply (simp add: drop_bit_bin_cat_eq take_bit_bin_cat_eq)
  done

lemma bin_rsplit_aux_len_le [rule_format] :
  "\<forall>ws m. n \<noteq> 0 \<longrightarrow> ws = bin_rsplit_aux n nw w bs \<longrightarrow>
    length ws \<le> m \<longleftrightarrow> nw + length bs * n \<le> m * n"
proof -
  have *: R
    if d: "i \<le> j \<or> m < j'"
    and R1: "i * k \<le> j * k \<Longrightarrow> R"
    and R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
    for i j j' k k' m :: nat and R
    using d
    apply safe
    apply (rule R1, erule mult_le_mono1)
    apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
    done
  have **: "0 < sc \<Longrightarrow> sc - n + (n + lb * n) \<le> m * n \<longleftrightarrow> sc + lb * n \<le> m * n"
    for sc m n lb :: nat
    apply safe
     apply arith
    apply (case_tac "sc \<ge> n")
     apply arith
    apply (insert linorder_le_less_linear [of m lb])
    apply (erule_tac k=n and k'=n in *)
     apply arith
    apply simp
    done
  show ?thesis
    apply (induct n nw w bs rule: bin_rsplit_aux.induct)
    apply (subst bin_rsplit_aux.simps)
    apply (simp add: ** Let_def split: prod.split)
    done
qed

lemma bin_rsplit_len_le: "n \<noteq> 0 \<longrightarrow> ws = bin_rsplit n (nw, w) \<longrightarrow> length ws \<le> m \<longleftrightarrow> nw \<le> m * n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len_le)

lemma bin_rsplit_aux_len:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit_aux n nw w cs) = (nw + n - 1) div n + length cs"
  apply (induct n nw w cs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (erule thin_rl)
  apply (case_tac m)
   apply simp
  apply (case_tac "m \<le> n")
   apply (auto simp add: div_add_self2)
  done

lemma bin_rsplit_len: "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, w)) = (nw + n - 1) div n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len)

lemma bin_rsplit_aux_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length bs = length cs \<Longrightarrow>
    length (bin_rsplit_aux n nw v bs) =
    length (bin_rsplit_aux n nw w cs)"
proof (induct n nw w cs arbitrary: v bs rule: bin_rsplit_aux.induct)
  case (1 n m w cs v bs)
  show ?case
  proof (cases "m = 0")
    case True
    with \<open>length bs = length cs\<close> show ?thesis by simp
  next
    case False
    from "1.hyps" [of \<open>bin_split n w\<close> \<open>drop_bit n w\<close> \<open>take_bit n w\<close>] \<open>m \<noteq> 0\<close> \<open>n \<noteq> 0\<close>
    have hyp: "\<And>v bs. length bs = Suc (length cs) \<Longrightarrow>
      length (bin_rsplit_aux n (m - n) v bs) =
      length (bin_rsplit_aux n (m - n) (drop_bit n w) (take_bit n w # cs))"
      using bin_rsplit_aux_len by fastforce
    from \<open>length bs = length cs\<close> \<open>n \<noteq> 0\<close> show ?thesis
      by (auto simp add: bin_rsplit_aux_simp_alt Let_def bin_rsplit_len split: prod.split)
  qed
qed

lemma bin_rsplit_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, v)) = length (bin_rsplit n (nw, w))"
  apply (unfold bin_rsplit_def)
  apply (simp (no_asm))
  apply (erule bin_rsplit_aux_len_indep)
  apply (rule refl)
  done


subsection \<open>Logical operations\<close>

primrec bin_sc :: "nat \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int"
  where
    Z: "bin_sc 0 b w = of_bool b + 2 * bin_rest w"
  | Suc: "bin_sc (Suc n) b w = of_bool (odd w) + 2 * bin_sc n b (w div 2)"

lemma bin_nth_sc [simp]: "bit (bin_sc n b w) n \<longleftrightarrow> b"
  by (induction n arbitrary: w) (simp_all add: bit_Suc)

lemma bin_sc_sc_same [simp]: "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induction n arbitrary: w) (simp_all add: bit_Suc)

lemma bin_sc_sc_diff: "m \<noteq> n \<Longrightarrow> bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: "bin_nth (bin_sc n b w) m = (if m = n then b else bin_nth w m)"
  apply (induct n arbitrary: w m)
   apply (case_tac m; simp add: bit_Suc)
  apply (case_tac m; simp add: bit_Suc)
  done

lemma bin_sc_eq:
  \<open>bin_sc n False = unset_bit n\<close>
  \<open>bin_sc n True = Bit_Operations.set_bit n\<close>
  by (simp_all add: fun_eq_iff bit_eq_iff)
    (simp_all add: bin_nth_sc_gen bit_set_bit_iff bit_unset_bit_iff)

lemma bin_sc_nth [simp]: "bin_sc n (bin_nth w n) w = w"
  by (rule bit_eqI) (simp add: bin_nth_sc_gen)

lemma bin_sign_sc [simp]: "bin_sign (bin_sc n b w) = bin_sign w"
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by (auto simp add: bin_sign_def) (use bin_rest_ge_0 in fastforce)
next
  case (Suc n)
  from Suc [of \<open>w div 2\<close>]
  show ?case by (auto simp add: bin_sign_def split: if_splits)
qed

lemma bin_sc_bintr [simp]:
  "bintrunc m (bin_sc n x (bintrunc m w)) = bintrunc m (bin_sc n x w)"
  apply (cases x)
   apply (simp_all add: bin_sc_eq bit_eq_iff)
   apply (auto simp add: bit_take_bit_iff bit_set_bit_iff bit_unset_bit_iff)
  done

lemma bin_clr_le: "bin_sc n False w \<le> w"
  by (simp add: bin_sc_eq unset_bit_less_eq)

lemma bin_set_ge: "bin_sc n True w \<ge> w"
  by (simp add: bin_sc_eq set_bit_greater_eq)

lemma bintr_bin_clr_le: "bintrunc n (bin_sc m False w) \<le> bintrunc n w"
  by (simp add: bin_sc_eq take_bit_unset_bit_eq unset_bit_less_eq)

lemma bintr_bin_set_ge: "bintrunc n (bin_sc m True w) \<ge> bintrunc n w"
  by (simp add: bin_sc_eq take_bit_set_bit_eq set_bit_greater_eq)

lemma bin_sc_FP [simp]: "bin_sc n False 0 = 0"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n True (- 1) = - 1"
  by (induct n) auto

lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus: "0 < n \<Longrightarrow> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus =
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc]

lemma bin_sc_numeral [simp]:
  "bin_sc (numeral k) b w =
    of_bool (odd w) + 2 * bin_sc (pred_numeral k) b (w div 2)"
  by (simp add: numeral_eq_Suc)

lemmas bin_sc_minus_simps =
  bin_sc_simps (2,3,4) [THEN [2] trans, OF bin_sc_minus [THEN sym]]

instance int :: semiring_bit_syntax ..

lemma test_bit_int_def [iff]:
  "i !! n \<longleftrightarrow> bin_nth i n"
  by (simp add: test_bit_eq_bit)

lemma shiftl_int_def:
  "shiftl x n = x * 2 ^ n" for x :: int
  by (simp add: push_bit_int_def shiftl_eq_push_bit)

lemma shiftr_int_def:
  "shiftr x n = x div 2 ^ n" for x :: int
  by (simp add: drop_bit_int_def shiftr_eq_drop_bit)


subsubsection \<open>Basic simplification rules\<close>

lemmas int_not_def = not_int_def

lemma int_not_simps [simp]:
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
  by (fact bit.conj_one_left)

lemma int_or_zero [simp]: "0 OR x = x"
  for x :: int
  by (fact bit.disj_zero_left)

lemma int_or_minus1 [simp]: "-1 OR x = -1"
  for x :: int
  by (fact bit.disj_one_left)

lemma int_xor_zero [simp]: "0 XOR x = x"
  for x :: int
  by (fact bit.xor_zero_left)


subsubsection \<open>Binary destructors\<close>

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (fact not_int_div_2)

lemma bin_last_NOT [simp]: "bin_last (NOT x) \<longleftrightarrow> \<not> bin_last x"
  by simp

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (subst and_int_rec) auto

lemma bin_last_AND [simp]: "bin_last (x AND y) \<longleftrightarrow> bin_last x \<and> bin_last y"
  by (subst and_int_rec) auto

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (subst or_int_rec) auto

lemma bin_last_OR [simp]: "bin_last (x OR y) \<longleftrightarrow> bin_last x \<or> bin_last y"
  by (subst or_int_rec) auto

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (subst xor_int_rec) auto

lemma bin_last_XOR [simp]: "bin_last (x XOR y) \<longleftrightarrow> (bin_last x \<or> bin_last y) \<and> \<not> (bin_last x \<and> bin_last y)"
  by (subst xor_int_rec) auto

lemma bin_nth_ops:
  "\<And>x y. bin_nth (x AND y) n \<longleftrightarrow> bin_nth x n \<and> bin_nth y n"
  "\<And>x y. bin_nth (x OR y) n \<longleftrightarrow> bin_nth x n \<or> bin_nth y n"
  "\<And>x y. bin_nth (x XOR y) n \<longleftrightarrow> bin_nth x n \<noteq> bin_nth y n"
  "\<And>x. bin_nth (NOT x) n \<longleftrightarrow> \<not> bin_nth x n"
  by (simp_all add: bit_and_iff bit_or_iff bit_xor_iff bit_not_iff)


subsubsection \<open>Derived properties\<close>

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


subsubsection \<open>Basic properties of logical (bit-wise) operations\<close>

lemma bbw_ao_absorb: "x AND (y OR x) = x \<and> x OR (y AND x) = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = x"
  "(y OR x) AND x = x \<and> x OR (x AND y) = x"
  "(x OR y) AND x = x \<and> (x AND y) OR x = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not: "(NOT x) XOR y = NOT (x XOR y) \<and> x XOR (NOT y) = NOT (x XOR y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_assoc: "(x AND y) AND z = x AND (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_assoc: "(x OR y) OR z = x OR (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_assoc: "(x XOR y) XOR z = x XOR (y XOR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]:
  "y AND (x AND z) = x AND (y AND z)"
  "y OR (x OR z) = x OR (y OR z)"
  "y XOR (x XOR z) = x XOR (y XOR z)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_not_dist:
  "NOT (x OR y) = (NOT x) AND (NOT y)"
  "NOT (x AND y) = (NOT x) OR (NOT y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_oa_dist: "(x AND y) OR z = (x OR z) AND (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_dist: "(x OR y) AND z = (x AND z) OR (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp]
*)


subsubsection \<open>Simplification with numerals\<close>

text \<open>Cases for \<open>0\<close> and \<open>-1\<close> are already covered by other simp rules.\<close>

lemma bin_rest_neg_numeral_BitM [simp]:
  "bin_rest (- numeral (Num.BitM w)) = - numeral w"
  by simp

lemma bin_last_neg_numeral_BitM [simp]:
  "bin_last (- numeral (Num.BitM w))"
  by simp


subsubsection \<open>Interactions with arithmetic\<close>

lemma le_int_or: "bin_sign y = 0 \<Longrightarrow> x \<le> x OR y"
  for x y :: int
  by (simp add: bin_sign_def or_greater_eq split: if_splits)

lemmas int_and_le =
  xtrans(3) [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

text \<open>Interaction between bit-wise and arithmetic: good example of \<open>bin_induction\<close>.\<close>
lemma bin_add_not: "x + NOT x = (-1::int)"
  by (simp add: not_int_def)

lemma AND_mod: "x AND (2 ^ n - 1) = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask mask_eq_exp_minus_1)


subsubsection \<open>Truncating results of bit-wise operations\<close>

lemma bin_trunc_ao:
  "bintrunc n x AND bintrunc n y = bintrunc n (x AND y)"
  "bintrunc n x OR bintrunc n y = bintrunc n (x OR y)"
  by simp_all

lemma bin_trunc_xor: "bintrunc n (bintrunc n x XOR bintrunc n y) = bintrunc n (x XOR y)"
  by simp

lemma bin_trunc_not: "bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  by (fact take_bit_not_take_bit)

text \<open>Want theorems of the form of \<open>bin_trunc_xor\<close>.\<close>
lemma bintr_bintr_i: "x = bintrunc n y \<Longrightarrow> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]


subsubsection \<open>More lemmas\<close>

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
  "bin_last i \<longleftrightarrow> i AND 1 \<noteq> 0"
  by (simp add: and_one_eq mod2_eq_if)

lemma bitval_bin_last:
  "of_bool (bin_last i) = i AND 1"
  by (simp add: and_one_eq mod2_eq_if)

lemma bin_sign_and:
  "bin_sign (i AND j) = - (bin_sign i * bin_sign j)"
by(simp add: bin_sign_def)

lemma int_not_neg_numeral: "NOT (- numeral n) = (Num.sub n num.One :: int)"
by(simp add: int_not_def)

lemma int_neg_numeral_pOne_conv_not: "- numeral (n + num.One) = (NOT (numeral n) :: int)"
by(simp add: int_not_def)


subsection \<open>Setting and clearing bits\<close>

lemma int_shiftl_BIT: fixes x :: int
  shows int_shiftl0 [simp]: "x << 0 = x"
  and int_shiftl_Suc [simp]: "x << Suc n = 2 * (x << n)"
  by (auto simp add: shiftl_int_def)

lemma int_0_shiftl [simp]: "0 << n = (0 :: int)"
by(induct n) simp_all

lemma bin_last_shiftl: "bin_last (x << n) \<longleftrightarrow> n = 0 \<and> bin_last x"
by(cases n)(simp_all)

lemma bin_rest_shiftl: "bin_rest (x << n) = (if n > 0 then x << (n - 1) else bin_rest x)"
by(cases n)(simp_all)

lemma bin_nth_shiftl [simp]: "bin_nth (x << n) m \<longleftrightarrow> n \<le> m \<and> bin_nth x (m - n)"
  by (simp add: bit_push_bit_iff_int shiftl_eq_push_bit)

lemma bin_last_shiftr: "odd (x >> n) \<longleftrightarrow> x !! n" for x :: int
  by (simp add: shiftr_eq_drop_bit bit_iff_odd_drop_bit)

lemma bin_rest_shiftr [simp]: "bin_rest (x >> n) = x >> Suc n"
  by (simp add: bit_eq_iff shiftr_eq_drop_bit drop_bit_Suc bit_drop_bit_eq drop_bit_half)

lemma bin_nth_shiftr [simp]: "bin_nth (x >> n) m = bin_nth x (n + m)"
  by (simp add: shiftr_eq_drop_bit bit_drop_bit_eq)

lemma bin_nth_conv_AND:
  fixes x :: int shows
  "bin_nth x n \<longleftrightarrow> x AND (1 << n) \<noteq> 0"
  by (simp add: bit_eq_iff)
    (auto simp add: shiftl_eq_push_bit bit_and_iff bit_push_bit_iff bit_exp_iff)

lemma int_shiftl_numeral [simp]:
  "(numeral w :: int) << numeral w' = numeral (num.Bit0 w) << pred_numeral w'"
  "(- numeral w :: int) << numeral w' = - numeral (num.Bit0 w) << pred_numeral w'"
by(simp_all add: numeral_eq_Suc shiftl_int_def)
  (metis add_One mult_inc semiring_norm(11) semiring_norm(13) semiring_norm(2) semiring_norm(6) semiring_norm(87))+

lemma int_shiftl_One_numeral [simp]:
  "(1 :: int) << numeral w = 2 << pred_numeral w"
  using int_shiftl_numeral [of Num.One w] by simp

lemma shiftl_ge_0 [simp]: fixes i :: int shows "i << n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(induct n) simp_all

lemma shiftl_lt_0 [simp]: fixes i :: int shows "i << n < 0 \<longleftrightarrow> i < 0"
by (metis not_le shiftl_ge_0)

lemma int_shiftl_test_bit: "(n << i :: int) !! m \<longleftrightarrow> m \<ge> i \<and> n !! (m - i)"
  by simp

lemma int_0shiftr [simp]: "(0 :: int) >> x = 0"
by(simp add: shiftr_int_def)

lemma int_minus1_shiftr [simp]: "(-1 :: int) >> x = -1"
by(simp add: shiftr_int_def div_eq_minus1)

lemma int_shiftr_ge_0 [simp]: fixes i :: int shows "i >> n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by (simp add: shiftr_eq_drop_bit)

lemma int_shiftr_lt_0 [simp]: fixes i :: int shows "i >> n < 0 \<longleftrightarrow> i < 0"
by (metis int_shiftr_ge_0 not_less)

lemma int_shiftr_numeral [simp]:
  "(1 :: int) >> numeral w' = 0"
  "(numeral num.One :: int) >> numeral w' = 0"
  "(numeral (num.Bit0 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(numeral (num.Bit1 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(- numeral (num.Bit0 w) :: int) >> numeral w' = - numeral w >> pred_numeral w'"
  "(- numeral (num.Bit1 w) :: int) >> numeral w' = - numeral (Num.inc w) >> pred_numeral w'"
  by (simp_all add: shiftr_eq_drop_bit numeral_eq_Suc add_One drop_bit_Suc)

lemma int_shiftr_numeral_Suc0 [simp]:
  "(1 :: int) >> Suc 0 = 0"
  "(numeral num.One :: int) >> Suc 0 = 0"
  "(numeral (num.Bit0 w) :: int) >> Suc 0 = numeral w"
  "(numeral (num.Bit1 w) :: int) >> Suc 0 = numeral w"
  "(- numeral (num.Bit0 w) :: int) >> Suc 0 = - numeral w"
  "(- numeral (num.Bit1 w) :: int) >> Suc 0 = - numeral (Num.inc w)"
  by (simp_all add: shiftr_eq_drop_bit drop_bit_Suc add_One)

lemma bin_nth_minus_p2:
  assumes sign: "bin_sign x = 0"
  and y: "y = 1 << n"
  and m: "m < n"
  and x: "x < y"
  shows "bin_nth (x - y) m = bin_nth x m"
proof -
  from sign y x have \<open>x \<ge> 0\<close> and \<open>y = 2 ^ n\<close> and \<open>x < 2 ^ n\<close>
    by (simp_all add: bin_sign_def shiftl_eq_push_bit push_bit_eq_mult split: if_splits)
  from \<open>0 \<le> x\<close> \<open>x < 2 ^ n\<close> \<open>m < n\<close> have \<open>bit x m \<longleftrightarrow> bit (x - 2 ^ n) m\<close>
  proof (induction m arbitrary: x n)
    case 0
    then show ?case
      by simp
  next
    case (Suc m)
    moreover define q where \<open>q = n - 1\<close>
    ultimately have n: \<open>n = Suc q\<close>
      by simp
    have \<open>(x - 2 ^ Suc q) div 2 = x div 2 - 2 ^ q\<close>
      by simp
    moreover from Suc.IH [of \<open>x div 2\<close> q] Suc.prems
    have \<open>bit (x div 2) m \<longleftrightarrow> bit (x div 2 - 2 ^ q) m\<close>
      by (simp add: n)
    ultimately show ?case
      by (simp add: bit_Suc n)
  qed
  with \<open>y = 2 ^ n\<close> show ?thesis
    by simp
qed

lemma bin_clr_conv_NAND:
  "bin_sc n False i = i AND NOT (1 << n)"
  by (induct n arbitrary: i) (rule bin_rl_eqI; simp)+

lemma bin_set_conv_OR:
  "bin_sc n True i = i OR (1 << n)"
  by (induct n arbitrary: i) (rule bin_rl_eqI; simp)+


subsection \<open>More lemmas on words\<close>

lemma word_rcat_eq:
  \<open>word_rcat ws = word_of_int (bin_rcat (LENGTH('a::len)) (map uint ws))\<close>
  for ws :: \<open>'a::len word list\<close>
  apply (simp add: word_rcat_def bin_rcat_def rev_map)
  apply transfer
  apply (simp add: horner_sum_foldr foldr_map comp_def)
  done

lemma sign_uint_Pls [simp]: "bin_sign (uint x) = 0"
  by (simp add: sign_Pls_ge_0)

lemmas bin_log_bintrs = bin_trunc_not bin_trunc_xor bin_trunc_and bin_trunc_or

\<comment> \<open>following definitions require both arithmetic and bit-wise word operations\<close>

\<comment> \<open>to get \<open>word_no_log_defs\<close> from \<open>word_log_defs\<close>, using \<open>bin_log_bintrs\<close>\<close>
lemmas wils1 = bin_log_bintrs [THEN word_of_int_eq_iff [THEN iffD2],
  folded uint_word_of_int_eq, THEN eq_reflection]

\<comment> \<open>the binary operations only\<close>  (* BH: why is this needed? *)
lemmas word_log_binary_defs =
  word_and_def word_or_def word_xor_def

lemma setBit_no [simp]: "setBit (numeral bin) n = word_of_int (bin_sc n True (numeral bin))"
  by transfer (simp add: bin_sc_eq)

lemma clearBit_no [simp]:
  "clearBit (numeral bin) n = word_of_int (bin_sc n False (numeral bin))"
  by transfer (simp add: bin_sc_eq)

lemma eq_mod_iff: "0 < n \<Longrightarrow> b = b mod n \<longleftrightarrow> 0 \<le> b \<and> b < n"
  for b n :: int
  by auto (metis pos_mod_conj)+

lemma split_uint_lem: "bin_split n (uint w) = (a, b) \<Longrightarrow>
    a = take_bit (LENGTH('a) - n) a \<and> b = take_bit (LENGTH('a)) b"
  for w :: "'a::len word"
  by transfer (simp add: drop_bit_take_bit ac_simps)

\<comment> \<open>limited hom result\<close>
lemma word_cat_hom:
  "LENGTH('a::len) \<le> LENGTH('b::len) + LENGTH('c::len) \<Longrightarrow>
    (word_cat (word_of_int w :: 'b word) (b :: 'c word) :: 'a word) =
    word_of_int (bin_cat w (size b) (uint b))"
  by transfer (simp add: take_bit_concat_bit_eq)

lemma bintrunc_shiftl:
  "take_bit n (m << i) = take_bit (n - i) m << i"
  for m :: int
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff)

lemma uint_shiftl:
  "uint (n << i) = take_bit (size n) (uint n << i)"
  by transfer (simp add: push_bit_take_bit shiftl_eq_push_bit)

lemma bin_mask_conv_pow2:
  "mask n = 2 ^ n - (1 :: int)"
  by (fact mask_eq_exp_minus_1)

lemma bin_mask_ge0: "mask n \<ge> (0 :: int)"
  by (fact mask_nonnegative_int)

lemma and_bin_mask_conv_mod: "x AND mask n = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask)

lemma bin_mask_numeral:
  "mask (numeral n) = (1 :: int) + 2 * mask (pred_numeral n)"
  by (fact mask_numeral)

lemma bin_nth_mask [simp]: "bit (mask n :: int) i \<longleftrightarrow> i < n"
  by (simp add: bit_mask_iff)

lemma bin_sign_mask [simp]: "bin_sign (mask n) = 0"
  by (simp add: bin_sign_def bin_mask_conv_pow2)

lemma bin_mask_p1_conv_shift: "mask n + 1 = (1 :: int) << n"
  by (simp add: bin_mask_conv_pow2 shiftl_int_def)

lemma sbintrunc_eq_in_range:
  "(sbintrunc n x = x) = (x \<in> range (sbintrunc n))"
  "(x = sbintrunc n x) = (x \<in> range (sbintrunc n))"
  apply (simp_all add: image_def)
  apply (metis sbintrunc_sbintrunc)+
  done

lemma sbintrunc_If:
  "- 3 * (2 ^ n) \<le> x \<and> x < 3 * (2 ^ n)
    \<Longrightarrow> sbintrunc n x = (if x < - (2 ^ n) then x + 2 * (2 ^ n)
        else if x \<ge> 2 ^ n then x - 2 * (2 ^ n) else x)"
  apply (simp add: no_sbintr_alt2, safe)
   apply (simp add: mod_pos_geq)
  apply (subst mod_add_self1[symmetric], simp)
  done

lemma sint_range':
  \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint x \<and> sint x < 2 ^ (LENGTH('a) - Suc 0)\<close>
  for x :: \<open>'a::len word\<close>
  apply transfer
  using sbintr_ge sbintr_lt apply auto
  done

lemma signed_arith_eq_checks_to_ord:
  "(sint a + sint b = sint (a + b ))
    = ((a <=s a + b) = (0 <=s b))"
  "(sint a - sint b = sint (a - b ))
    = ((0 <=s a - b) = (b <=s a))"
  "(- sint a = sint (- a)) = (0 <=s (- a) = (a <=s 0))"
  using sint_range'[where x=a] sint_range'[where x=b]
  by (simp_all add: sint_word_ariths word_sle_eq word_sless_alt sbintrunc_If)

lemma signed_mult_eq_checks_double_size:
  assumes mult_le: "(2 ^ (len_of TYPE ('a) - 1) + 1) ^ 2 \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
           and le: "2 ^ (LENGTH('a) - 1) \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
  shows "(sint (a :: 'a :: len word) * sint b = sint (a * b))
       = (scast a * scast b = (scast (a * b) :: 'b :: len word))"
proof -
  have P: "sbintrunc (size a - 1) (sint a * sint b) \<in> range (sbintrunc (size a - 1))"
    by simp

  have abs: "!! x :: 'a word. abs (sint x) < 2 ^ (size a - 1) + 1"
    apply (cut_tac x=x in sint_range')
    apply (simp add: abs_le_iff word_size)
    done
  have abs_ab: "abs (sint a * sint b) < 2 ^ (LENGTH('b) - 1)"
    using abs_mult_less[OF abs[where x=a] abs[where x=b]] mult_le
    by (simp add: abs_mult power2_eq_square word_size)
  define r s where \<open>r = LENGTH('a) - 1\<close> \<open>s = LENGTH('b) - 1\<close>
  then have \<open>LENGTH('a) = Suc r\<close> \<open>LENGTH('b) = Suc s\<close>
    \<open>size a = Suc r\<close> \<open>size b = Suc r\<close>
    by (simp_all add: word_size)
  then show ?thesis
    using P[unfolded range_sbintrunc] abs_ab le
    apply clarsimp
    apply (transfer fixing: r s)
    apply (auto simp add: signed_take_bit_int_eq_self simp flip: signed_take_bit_eq_iff_take_bit_eq)
    done
qed

code_identifier
  code_module Bits_Int \<rightharpoonup>
  (SML) Bit_Operations and (OCaml) Bit_Operations and (Haskell) Bit_Operations and (Scala) Bit_Operations

end
