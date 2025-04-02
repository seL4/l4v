(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Lemmas on division\<close>

theory More_Divides
  imports
    "HOL-Library.Word"
begin

declare div_eq_dividend_iff [simp]

lemma int_div_same_is_1 [simp]:
  \<open>a div b = a \<longleftrightarrow> b = 1\<close> if \<open>0 < a\<close> for a b :: int
  by (metis div_by_1 int_div_less_self less_le_not_le nle_le nonneg1_imp_zdiv_pos_iff that)

lemma int_div_minus_is_minus1 [simp]:
  \<open>a div b = - a \<longleftrightarrow> b = - 1\<close> if \<open>0 > a\<close> for a b :: int
  using that by (metis div_minus_right equation_minus_iff int_div_same_is_1 neg_0_less_iff_less)

lemma nat_div_eq_Suc_0_iff: "n div m = Suc 0 \<longleftrightarrow> m \<le> n \<and> n < 2 * m" (is "?L=?R")
proof
  show "?L\<Longrightarrow>?R"
    by (metis div_greater_zero_iff div_less_iff_less_mult lessI numeral_2_eq_2)
qed (simp add: div_nat_eqI)

lemma diff_mod_le:
  \<open>a - a mod b \<le> d - b\<close> if \<open>a < d\<close> \<open>b dvd d\<close> for a b d :: nat
proof(cases \<open>b = 0\<close>)
  case True
  then show ?thesis
    by auto
next
  case False
  then obtain k where k: "d = b * k"
    using \<open>b dvd d\<close> by blast
  then have "a div b < k"
    by (metis less_mult_imp_div_less mult.commute that(1))
  then have "b * (a div b) \<le> b * (k - 1)"
    by auto
  then show ?thesis
    by (simp add: k minus_mod_eq_mult_div right_diff_distrib')
qed

lemma one_mod_exp_eq_one [simp]:
  "1 mod (2 * 2 ^ n) = (1::int)"
  using power_gt1 [of 2 n] by (auto intro: mod_pos_pos_trivial)

lemma int_mod_lem: "0 < n \<Longrightarrow> 0 \<le> b \<and> b < n \<longleftrightarrow> b mod n = b"
  for b n :: int
  using zmod_trivial_iff by force

lemma int_mod_ge': "b < 0 \<Longrightarrow> 0 < n \<Longrightarrow> b + n \<le> b mod n"
  for b n :: int
  by (metis add_less_same_cancel2 int_mod_ge mod_add_self2)

lemma int_mod_le': "0 \<le> b - n \<Longrightarrow> b mod n \<le> b - n"
  for b n :: int
  by (metis minus_mod_self2 zmod_le_nonneg_dividend)

lemma emep1: "even n \<Longrightarrow> even d \<Longrightarrow> 0 \<le> d \<Longrightarrow> (n + 1) mod d = (n mod d) + 1"
  for n d :: int
  by (auto simp add: pos_zmod_mult_2 add.commute dvd_def)

lemma m1mod2k: "- 1 mod 2 ^ n = (2 ^ n - 1 :: int)"
  by (rule zmod_minus1) simp

lemma sb_inc_lem: "a + 2^k < 0 \<Longrightarrow> a + 2^k + 2^(Suc k) \<le> (a + 2^k) mod 2^(Suc k)"
  for a :: int
  using int_mod_ge' [where n = "2 ^ (Suc k)" and b = "a + 2 ^ k"]
  by simp

lemma sb_inc_lem': "a < - (2^k) \<Longrightarrow> a + 2^k + 2^(Suc k) \<le> (a + 2^k) mod 2^(Suc k)"
  for a :: int
  by (rule sb_inc_lem) simp

lemma sb_dec_lem: "0 \<le> - (2 ^ k) + a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  for a :: int
  using int_mod_le'[where n = "2 ^ (Suc k)" and b = "a + 2 ^ k"] by simp

lemma sb_dec_lem': "2 ^ k \<le> a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  for a :: int
  by (rule sb_dec_lem) simp

lemma mod_2_neq_1_eq_eq_0: "k mod 2 \<noteq> 1 \<longleftrightarrow> k mod 2 = 0"
  for k :: int
  by (fact not_mod_2_eq_1_eq_0)

lemma z1pmod2: "(2 * b + 1) mod 2 = (1::int)"
  for b :: int
  by arith

lemma p1mod22k': "(1 + 2 * b) mod (2 * 2 ^ n) = 1 + 2 * (b mod 2 ^ n)"
  for b :: int
  by (rule pos_zmod_mult_2) simp

lemma p1mod22k: "(2 * b + 1) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n) + 1"
  for b :: int
  by (simp add: p1mod22k' add.commute)

lemma pos_mod_sign2:
  \<open>0 \<le> a mod 2\<close> for a :: int
  by simp

lemma pos_mod_bound2:
  \<open>a mod 2 < 2\<close> for a :: int
  by simp

lemma nmod2: "n mod 2 = 0 \<or> n mod 2 = 1"
  for n :: int
  by arith

lemma eme1p:
  "even n \<Longrightarrow> even d \<Longrightarrow> 0 \<le> d \<Longrightarrow> (1 + n) mod d = 1 + n mod d" for n d :: int
  using emep1 [of n d] by (simp add: ac_simps)

lemma m1mod22k:
  \<open>- 1 mod (2 * 2 ^ n) = 2 * 2 ^ n - (1::int)\<close>
  by (simp add: zmod_minus1)

lemma z1pdiv2: "(2 * b + 1) div 2 = b"
  for b :: int
  by arith

lemma zdiv_le_dividend:
  \<open>0 \<le> a \<Longrightarrow> 0 < b \<Longrightarrow> a div b \<le> a\<close> for a b :: int
  by (metis div_by_1 int_one_le_iff_zero_less zdiv_mono2 zero_less_one)

lemma axxmod2: "(1 + x + x) mod 2 = 1 \<and> (0 + x + x) mod 2 = 0"
  for x :: int
  by arith

lemma axxdiv2: "(1 + x + x) div 2 = x \<and> (0 + x + x) div 2 = x"
  for x :: int
  by arith

lemmas rdmods =
  mod_minus_eq [symmetric]
  mod_diff_left_eq [symmetric]
  mod_diff_right_eq [symmetric]
  mod_add_left_eq [symmetric]
  mod_add_right_eq [symmetric]
  mod_mult_right_eq [symmetric]
  mod_mult_left_eq [symmetric]

lemma mod_plus_right: "(a + x) mod m = (b + x) mod m \<longleftrightarrow> a mod m = b mod m"
  for a b m x :: nat
  by (induct x) (simp_all add: mod_Suc, arith)

lemma nat_minus_mod: "(n - n mod m) mod m = 0"
  for m n :: nat
  by (induct n) (simp_all add: mod_Suc)

lemmas nat_minus_mod_plus_right =
  trans [OF nat_minus_mod mod_0 [symmetric],
    THEN mod_plus_right [THEN iffD2], simplified]

lemmas push_mods' = mod_add_eq
  mod_mult_eq mod_diff_eq
  mod_minus_eq

lemmas push_mods = push_mods' [THEN eq_reflection]
lemmas pull_mods = push_mods [symmetric] rdmods [THEN eq_reflection]

lemma nat_mod_eq: "b < n \<Longrightarrow> a mod n = b mod n \<Longrightarrow> a mod n = b"
  for a b n :: nat
  by (induct a) auto

lemmas nat_mod_eq' = refl [THEN [2] nat_mod_eq]

lemma nat_mod_lem: "0 < n \<Longrightarrow> b < n \<longleftrightarrow> b mod n = b"
  for b n :: nat
  by (metis mod_less_divisor nat_mod_eq')

lemma mod_nat_add: "x < z \<Longrightarrow> y < z \<Longrightarrow> (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: nat
  using mod_if by auto

lemma mod_nat_sub: "x < z \<Longrightarrow> (x - y) mod z = x - y"
  for x y :: nat
  by simp

lemma int_mod_eq: "0 \<le> b \<Longrightarrow> b < n \<Longrightarrow> a mod n = b mod n \<Longrightarrow> a mod n = b"
  for a b n :: int
  by (metis mod_pos_pos_trivial)

lemma zmde:
  \<open>b * (a div b) = a - a mod b\<close> for a b :: \<open>'a::{group_add,semiring_modulo}\<close>
  using mult_div_mod_eq [of b a] by (simp add: eq_diff_eq)

(* already have this for naturals, div_mult_self1/2, but not for ints *)
lemma zdiv_mult_self: "m \<noteq> 0 \<Longrightarrow> (a + m * n) div m = a div m + n"
  for a m n :: int
  by simp

lemma mod_power_lem: "a > 1 \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  for a :: int
  by (simp add: mod_eq_0_iff_dvd le_imp_power_dvd)

lemma nonneg_mod_div: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> (a mod b) \<and> 0 \<le> a div b"
  for a b :: int
  by (cases "b = 0") (auto intro: pos_imp_zdiv_nonneg_iff [THEN iffD2])

lemma mod_exp_less_eq_exp:
  \<open>a mod 2 ^ n < 2 ^ n\<close> for a :: int
  by (rule pos_mod_bound) simp

lemma div_mult_le:
  \<open>a div b * b \<le> a\<close> for a b :: nat
  by (fact div_times_less_eq_dividend)

lemma power_sub:
  fixes a :: nat
  assumes lt: "n \<le> m"
  and     av: "0 < a"
  shows "a ^ (m - n) = a ^ m div a ^ n"
  using av less_irrefl lt power_diff by blast

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  using mod_less_divisor [where m = q and n = c]
  by (smt (verit) div_eq_0_iff add.right_neutral div_mult2_eq div_mult_self3 not_less0 mult.commute)

lemma less_two_pow_divD:
  "\<lbrakk> (x :: nat) < 2 ^ n div 2 ^ m \<rbrakk> \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  by (metis One_nat_def div_less lessI not_less0 linorder_not_le numeral_2_eq_2 power_diff power_increasing_iff)

lemma less_two_pow_divI:
  "\<lbrakk> (x :: nat) < 2 ^ (n - m); m \<le> n \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  by (simp add: power_sub)

lemmas m2pths = pos_mod_sign mod_exp_less_eq_exp

lemma power_mod_div:
  fixes x :: "nat"
  shows "x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)" (is "?LHS = ?RHS")
proof (cases "n \<le> m")
  case True
  then have "?LHS = 0"
    by (metis diff_is_0_eq' drop_bit_eq_div drop_bit_take_bit take_bit_0 take_bit_eq_mod)
  also have "\<dots> = ?RHS" using True
    by simp
  finally show ?thesis .
next
  case False
  then have lt: "m < n" by simp
  then obtain q where nv: "n = m + q" and "0 < q"
    by (auto dest: less_imp_Suc_add)

  then have "x mod 2 ^ n = 2 ^ m * (x div 2 ^ m mod 2 ^ q) + x mod 2 ^ m"
    by (simp add: power_add mod_mult2_eq)

  then have "?LHS = x div 2 ^ m mod 2 ^ q"
    by (simp add: div_add1_eq)

  also have "\<dots> = ?RHS" using nv
    by simp

  finally show ?thesis .
qed

lemma mod_div_equality_div_eq:
  "a div b * b = (a - (a mod b) :: int)"
  by (simp add: field_simps)

lemma zmod_helper:
  "n mod m = k \<Longrightarrow> ((n :: int) + a) mod m = (k + a) mod m"
  by (metis add.commute mod_add_right_eq)

lemma int_div_sub_1:
  assumes "m \<ge> 1"
  shows "(n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
proof -
  have "(n - 1) div m * m = n div m * m - 1 * m" if "m dvd n"
  proof (cases "m = 1")
    case False
    with that show ?thesis
      using assms
      unfolding mod_div_equality_div_eq
      by (smt (verit, ccfv_SIG) dvd_eq_mod_eq_0 int_mod_ge' mod_diff_eq pos_mod_bound pos_mod_sign)
  qed auto
  moreover
  have "\<not> m dvd n \<Longrightarrow> (n - 1) div m * m = n div m * m"
    by (smt (verit, del_insts) assms mod_0_imp_dvd pos_zdiv_mult_2 zdiv_mono1 zdiv_zminus1_eq_if)
  ultimately
  have "m = 0 \<or> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
    by (metis left_diff_distrib' mult.commute nonzero_mult_div_cancel_left)
  then show ?thesis
    using assms by force
qed

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  by (simp add: power_diff)

lemma two_pow_div_gt_le:
  "v < 2 ^ n div (2 ^ m :: nat) \<Longrightarrow> m \<le> n"
  using less_two_pow_divD by blast

lemma td_gal_lt:
  \<open>0 < c \<Longrightarrow> a < b * c \<longleftrightarrow> a div c < b\<close>
  for a b c :: nat
  by (simp add: div_less_iff_less_mult)

lemma td_gal:
  \<open>0 < c \<Longrightarrow> b * c \<le> a  \<longleftrightarrow> b \<le> a div c\<close>
  for a b c :: nat
  by (simp add: less_eq_div_iff_mult_less_eq)

end
