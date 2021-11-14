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
  using that by (metis div_by_1 abs_ge_zero abs_of_pos int_div_less_self neq_iff
            nonneg1_imp_zdiv_pos_iff zabs_less_one_iff)

lemma int_div_minus_is_minus1 [simp]:
  \<open>a div b = - a \<longleftrightarrow> b = - 1\<close> if \<open>0 > a\<close> for a b :: int
  using that by (metis div_minus_right equation_minus_iff int_div_same_is_1 neg_0_less_iff_less)

lemma nat_div_eq_Suc_0_iff: "n div m = Suc 0 \<longleftrightarrow> m \<le> n \<and> n < 2 * m"
  apply auto
  using div_greater_zero_iff apply fastforce
   apply (metis One_nat_def div_greater_zero_iff dividend_less_div_times mult.right_neutral mult_Suc mult_numeral_1 numeral_2_eq_2 zero_less_numeral)
  apply (simp add: div_nat_eqI)
  done

lemma diff_mod_le:
  \<open>a - a mod b \<le> d - b\<close> if \<open>a < d\<close> \<open>b dvd d\<close> for a b d :: nat
  using that
  apply(subst minus_mod_eq_mult_div)
  apply(clarsimp simp: dvd_def)
  apply(cases \<open>b = 0\<close>)
   apply simp
  apply(subgoal_tac "a div b \<le> k - 1")
   prefer 2
   apply(subgoal_tac "a div b < k")
    apply(simp add: less_Suc_eq_le [symmetric])
   apply(subgoal_tac "b * (a div b) < b * ((b * k) div b)")
    apply clarsimp
   apply(subst div_mult_self1_is_m)
    apply arith
   apply(rule le_less_trans)
    apply simp
    apply(subst mult.commute)
    apply(rule div_times_less_eq_dividend)
   apply assumption
  apply clarsimp
  apply(subgoal_tac "b * (a div b) \<le> b * (k - 1)")
   apply(erule le_trans)
   apply(simp add: diff_mult_distrib2)
  apply simp
  done

lemma one_mod_exp_eq_one [simp]:
  "1 mod (2 * 2 ^ n) = (1::int)"
  using power_gt1 [of 2 n] by (auto intro: mod_pos_pos_trivial)

lemma int_mod_lem: "0 < n \<Longrightarrow> 0 \<le> b \<and> b < n \<longleftrightarrow> b mod n = b"
  for b n :: int
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done

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
  apply safe
   apply (erule nat_mod_eq')
  apply (erule subst)
  apply (erule mod_less_divisor)
  done

lemma mod_nat_add: "x < z \<Longrightarrow> y < z \<Longrightarrow> (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: nat
  apply (rule nat_mod_eq)
   apply auto
  apply (rule trans)
   apply (rule le_mod_geq)
   apply simp
  apply (rule nat_mod_eq')
  apply arith
  done

lemma mod_nat_sub: "x < z \<Longrightarrow> (x - y) mod z = x - y"
  for x y :: nat
  by (rule nat_mod_eq') arith

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

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  apply (cut_tac m = q and n = c in mod_less_divisor)
  apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
  apply (erule_tac P = "%x. lhs < rhs x" for lhs rhs in ssubst)
  apply (simp add: add_mult_distrib2)
  done

lemma less_two_pow_divD:
  "\<lbrakk> (x :: nat) < 2 ^ n div 2 ^ m \<rbrakk>
    \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (rule context_conjI)
   apply (rule ccontr)
   apply (simp add: power_strict_increasing)
  apply (simp add: power_sub)
  done

lemma less_two_pow_divI:
  "\<lbrakk> (x :: nat) < 2 ^ (n - m); m \<le> n \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  by (simp add: power_sub)

lemmas m2pths = pos_mod_sign mod_exp_less_eq_exp

lemmas int_mod_eq' = mod_pos_pos_trivial (* FIXME delete *)

lemmas int_mod_le = zmod_le_nonneg_dividend (* FIXME: delete *)

lemma power_mod_div:
  fixes x :: "nat"
  shows "x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)" (is "?LHS = ?RHS")
proof (cases "n \<le> m")
  case True
  then have "?LHS = 0"
    apply -
    apply (rule div_less)
    apply (rule order_less_le_trans [OF mod_less_divisor]; simp)
    done
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

lemma mod_mod_power:
  fixes k :: nat
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
proof (cases "m \<le> n")
  case True

  then have "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ m"
    apply -
    apply (subst mod_less [where n = "2 ^ n"])
    apply (rule order_less_le_trans [OF mod_less_divisor])
    apply simp+
    done
  also have "\<dots> = k mod  2 ^ (min m n)" using True by simp
  finally show ?thesis .
next
  case False
  then have "n < m" by simp
  then obtain d where md: "m = n + d"
    by (auto dest: less_imp_add_positive)
  then have "k mod 2 ^ m = 2 ^ n * (k div 2 ^ n mod 2 ^ d) + k mod 2 ^ n"
    by (simp add: mod_mult2_eq power_add)
  then have "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ n"
    by (simp add: mod_add_left_eq)
  then show ?thesis using False
    by simp
qed

lemma mod_div_equality_div_eq:
  "a div b * b = (a - (a mod b) :: int)"
  by (simp add: field_simps)

lemma zmod_helper:
  "n mod m = k \<Longrightarrow> ((n :: int) + a) mod m = (k + a) mod m"
  by (metis add.commute mod_add_right_eq)

lemma int_div_sub_1:
  "\<lbrakk> m \<ge> 1 \<rbrakk> \<Longrightarrow> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
  apply (subgoal_tac "m = 0 \<or> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)")
   apply fastforce
  apply (subst mult_cancel_right[symmetric])
  apply (simp only: left_diff_distrib split: if_split)
  apply (simp only: mod_div_equality_div_eq)
  apply (clarsimp simp: field_simps)
  apply (clarsimp simp: dvd_eq_mod_eq_0)
  apply (cases "m = 1")
   apply simp
  apply (subst mod_diff_eq[symmetric], simp add: zmod_minus1)
  apply clarsimp
  apply (subst diff_add_cancel[where b=1, symmetric])
  apply (subst mod_add_eq[symmetric])
  apply (simp add: field_simps)
  apply (rule mod_pos_pos_trivial)
   apply (subst add_0_right[where a=0, symmetric])
   apply (rule add_mono)
    apply simp
   apply simp
  apply (cases "(n - 1) mod m = m - 1")
   apply (drule zmod_helper[where a=1])
   apply simp
  apply (subgoal_tac "1 + (n - 1) mod m \<le> m")
   apply simp
  apply (subst field_simps, rule zless_imp_add1_zle)
  apply simp
  done

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  apply (induct a arbitrary: b)
   apply simp
  apply (erule le_SucE)
   apply (clarsimp simp:Suc_diff_le le_iff_add power_add)
  apply simp
  done

lemma two_pow_div_gt_le:
  "v < 2 ^ n div (2 ^ m :: nat) \<Longrightarrow> m \<le> n"
  by (clarsimp dest!: less_two_pow_divD)

lemma td_gal_lt:
  \<open>0 < c \<Longrightarrow> a < b * c \<longleftrightarrow> a div c < b\<close>
  for a b c :: nat
  by (simp add: div_less_iff_less_mult)

lemma td_gal:
  \<open>0 < c \<Longrightarrow> b * c \<le> a  \<longleftrightarrow> b \<le> a div c\<close>
  for a b c :: nat
  by (simp add: less_eq_div_iff_mult_less_eq)

end
