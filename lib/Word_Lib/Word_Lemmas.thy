(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
Proofs tidied by LCP, 2024-09
 *)

section "Lemmas with Generic Word Length"

theory Word_Lemmas
  imports
    Type_Syntax
    Signed_Division_Word
    Signed_Words
    More_Word
    Most_significant_bit
    Enumeration_Word
    Aligned
    Bit_Shifts_Infix_Syntax
    Boolean_Inequalities
    Word_EqI

begin

lemmas take_bit_Suc_numeral[simp] = take_bit_Suc[where a="numeral w" for w]

context
  includes bit_operations_syntax
begin

lemma word_max_le_or:
  "max x y \<le> x OR y" for x :: "'a::len word"
  by (simp add: word_bool_le_funs)

lemma word_and_le_min:
  "x AND y \<le> min x y" for x :: "'a::len word"
  by (simp add: word_bool_le_funs)

lemma word_not_le_eq:
  "(NOT x \<le> y) = (NOT y \<le> x)" for x :: "'a::len word"
  by transfer (auto simp: take_bit_not_eq_mask_diff)

lemma word_not_le_not_eq[simp]:
  "(NOT y \<le> NOT x) = (x \<le> y)" for x :: "'a::len word"
  by (subst word_not_le_eq) simp

lemma not_min_eq:
  "NOT (min x y) = max (NOT x) (NOT y)" for x :: "'a::len word"
  unfolding min_def max_def
  by auto

lemma not_max_eq:
  "NOT (max x y) = min (NOT x) (NOT y)" for x :: "'a::len word"
  unfolding min_def max_def
  by auto

lemma ucast_le_ucast_eq:
  fixes x y :: "'a::len word"
  assumes x: "x < 2 ^ n"
  assumes y: "y < 2 ^ n"
  assumes n: "n = LENGTH('b::len)"
  shows "(UCAST('a \<rightarrow> 'b) x \<le> UCAST('a \<rightarrow> 'b) y) \<longleftrightarrow> (x \<le> y)" (is "?L=_")
proof
  assume ?L then show "x \<le> y"
    by (metis x less_mask_eq le_ucast_ucast_le n ucast_ucast_mask)
qed (use n ucast_mono_le y in auto)

lemma ucast_zero_is_aligned:
  \<open>is_aligned w n\<close> if \<open>UCAST('a::len \<rightarrow> 'b::len) w = 0\<close> \<open>n \<le> LENGTH('b)\<close>
proof (rule is_aligned_bitI)
  fix q
  assume \<open>q < n\<close>
  moreover have \<open>bit (UCAST('a::len \<rightarrow> 'b::len) w) q = bit 0 q\<close>
    using that by simp
  with \<open>q < n\<close> \<open>n \<le> LENGTH('b)\<close> show \<open>\<not> bit w q\<close>
    by (simp add: bit_simps)
qed

lemma unat_ucast_eq_unat_and_mask:
  "unat (UCAST('b::len \<rightarrow> 'a::len) w) = unat (w AND mask LENGTH('a))"
  by (metis take_bit_eq_mask unsigned_take_bit_eq unsigned_ucast_eq)

lemma le_max_word_ucast_id:
  \<open>UCAST('b \<rightarrow> 'a) (UCAST('a \<rightarrow> 'b) x) = x\<close>
    if \<open>x \<le> UCAST('b::len \<rightarrow> 'a) (- 1)\<close>
    for x :: \<open>'a::len word\<close>
proof -
  from that have a1: \<open>x \<le> word_of_int (uint (word_of_int (2 ^ LENGTH('b) - 1) :: 'b word))\<close>
    by (simp add: of_int_mask_eq)
  have f2: "((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
            \<not> (0::int) \<le> - 1 + 2 ^ LENGTH('b) \<or> (0::int) \<le> - 1 + 2 ^ LENGTH('b) + - 1 * 2 ^ LENGTH('b) \<or>
            (- (1::int) + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b) =
              - 1 + 2 ^ LENGTH('b)) = ((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
            \<not> (1::int) \<le> 2 ^ LENGTH('b) \<or>
            2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)) = 1)"
    by force
  have f3: "\<forall>i ia. \<not> (0::int) \<le> i \<or> 0 \<le> i + - 1 * ia \<or> i mod ia = i"
    using mod_pos_pos_trivial by force
  have "(1::int) \<le> 2 ^ LENGTH('b)"
    by simp
  then have "2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ len_of TYPE ('b)) = 1"
    using f3 f2 by blast
  then have f4: "- (1::int) + 2 ^ LENGTH('b) = (- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)"
    by linarith
  have f5: "x \<le> word_of_int (uint (word_of_int (- 1 + 2 ^ LENGTH('b))::'b word))"
    using a1 by force
  have f6: "2 ^ LENGTH('b) + - (1::int) = - 1 + 2 ^ LENGTH('b)"
    by force
  have f7: "- (1::int) * 1 = - 1"
    by auto
  have "\<forall>x0 x1. (x1::int) - x0 = x1 + - 1 * x0"
    by force
  then have \<section>: "x \<le> 2 ^ LENGTH('b) - 1"
    using f7 f6 f5 f4 by (metis uint_word_of_int wi_homs(2) word_arith_wis(8) word_of_int_2p)
  then have \<open>uint x \<le> uint (2 ^ LENGTH('b) - (1 :: 'a word))\<close>
    by (simp add: word_le_def)
  then have \<open>uint x \<le> 2 ^ LENGTH('b) - 1\<close>
    by (simp add: uint_word_ariths)
      (metis \<open>1 \<le> 2 ^ LENGTH('b)\<close> \<open>uint x \<le> uint (2 ^ LENGTH('b) - 1)\<close> linorder_not_less lt2p_lem uint_1 uint_minus_simple_alt uint_power_lower word_le_def zle_diff1_eq)
  then show ?thesis
    by (metis \<section> and_mask_eq_iff_le_mask mask_eq_exp_minus_1 ucast_ucast_mask)
qed

lemma uint_shiftr_eq:
  \<open>uint (w >> n) = uint w div 2 ^ n\<close>
  by word_eqI

lemma bit_shiftl_word_iff [bit_simps]:
  \<open>bit (w << m) n \<longleftrightarrow> m \<le> n \<and> n < LENGTH('a) \<and> bit w (n - m)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: bit_simps)

lemma bit_shiftr_word_iff:
  \<open>bit (w >> m) n \<longleftrightarrow> bit w (m + n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: bit_simps)

lemma uint_sshiftr_eq:
  \<open>uint (w >>> n) = take_bit LENGTH('a) (sint w div 2 ^  n)\<close>
  for w :: \<open>'a::len word\<close>
  by (word_eqI_solve dest: test_bit_lenD)

lemma sshiftr_n1: "-1 >>> n = -1"
  by (simp add: sshiftr_def)

lemma nth_sshiftr:
  "bit (w >>> m) n = (n < size w \<and> (if n + m \<ge> size w then bit w (size w - 1) else bit w (n + m)))"
  by (simp add: add.commute bit_sshiftr_iff test_bit_over wsst_TYs(3))

lemma sshiftr_numeral:
  \<open>(numeral k >>> numeral n :: 'a::len word) =
    word_of_int (signed_take_bit (LENGTH('a) - 1) (numeral k) >> numeral n)\<close>
  using signed_drop_bit_word_numeral [of n k] by (simp add: sshiftr_def shiftr_def)

lemma sshiftr_div_2n: "sint (w >>> n) = sint w div 2 ^ n"
  by word_eqI (cases \<open>n < LENGTH('a)\<close>; fastforce simp: le_diff_conv2)

lemma mask_eq:
  \<open>mask n = (1 << n) - (1 :: 'a::len word)\<close>
  by (simp add: mask_eq_exp_minus_1 shiftl_def)

lemma nth_shiftl': "bit (w << m) n \<longleftrightarrow> n < size w \<and> n >= m \<and> bit w (n - m)"
  for w :: "'a::len word"
  by (simp add: bit_simps word_size ac_simps)

lemmas nth_shiftl = nth_shiftl' [unfolded word_size]

lemma nth_shiftr: "bit (w >> m) n = bit w (n + m)"
  for w :: "'a::len word"
  by (simp add: bit_simps ac_simps)

lemma shiftr_div_2n: "uint (shiftr w n) = uint w div 2 ^ n"
  by (fact uint_shiftr_eq)

lemma shiftl_rev: "shiftl w n = word_reverse (shiftr (word_reverse w) n)"
  by word_eqI_solve

lemma rev_shiftl: "word_reverse w << n = word_reverse (w >> n)"
  by (simp add: shiftl_rev)

lemma shiftr_rev: "w >> n = word_reverse (word_reverse w << n)"
  by (simp add: rev_shiftl)

lemma rev_shiftr: "word_reverse w >> n = word_reverse (w << n)"
  by (simp add: shiftr_rev)

lemmas ucast_up =
  rc1 [simplified rev_shiftr [symmetric] revcast_ucast [symmetric]]
lemmas ucast_down =
  rc2 [simplified rev_shiftr revcast_ucast [symmetric]]

lemma shiftl_zero_size: "size x \<le> n \<Longrightarrow> x << n = 0"
  for x :: "'a::len word"
  by (simp add: shiftl_def word_size)

lemma shiftl_t2n: "shiftl w n = 2 ^ n * w"
  for w :: "'a::len word"
  by (simp add: shiftl_def push_bit_eq_mult)

lemma word_shift_by_2:
  "x * 4 = (x::'a::len word) << 2"
  by (simp add: shiftl_t2n)

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  by word_eqI (cases \<open>n \<le> LENGTH('b)\<close>; fastforce simp: ac_simps dest: bit_imp_le_length)

lemma shiftr_zero_size: "size x \<le> n \<Longrightarrow> x >> n = 0"
  for x :: "'a :: len word"
  by word_eqI

lemma shiftr_x_0 [simp]: "x >> 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftr_def)

lemma shiftl_x_0 [simp]: "x << 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftl_def)

lemmas shiftl0 = shiftl_x_0

lemma shiftr_1 [simp]: "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (simp add: shiftr_def)

lemma and_not_mask:
  "w AND NOT (mask n) = (w >> n) << n"
  for w :: \<open>'a::len word\<close>
  by word_eqI_solve

lemma and_mask:
  "w AND mask n = (w << (size w - n)) >> (size w - n)"
  for w :: \<open>'a::len word\<close>
  by word_eqI_solve

lemma shiftr_div_2n_w: "w >> n = w div (2^n :: 'a :: len word)"
  by (fact shiftr_eq_div)

lemma le_shiftr:
  "u \<le> v \<Longrightarrow> u >> (n :: nat) \<le> (v :: 'a :: len word) >> n"
  unfolding shiftr_def
  apply transfer
  apply (simp add: take_bit_drop_bit)
  apply (simp add: drop_bit_eq_div zdiv_mono1)
  done

lemma le_shiftr':
  "\<lbrakk> u >> n \<le> v >> n ; u >> n \<noteq> v >> n \<rbrakk> \<Longrightarrow> (u::'a::len word) \<le> v"
  by (metis le_cases le_shiftr verit_la_disequality)

lemma shiftr_mask_le:
  "n \<le> m \<Longrightarrow> mask n >> m = (0 :: 'a::len word)"
  by word_eqI

lemma shiftr_mask [simp]:
  \<open>mask m >> m = (0::'a::len word)\<close>
  by (rule shiftr_mask_le) simp

lemma le_mask_iff:
  "(w \<le> mask n) = (w >> n = 0)"
  for w :: \<open>'a::len word\<close>
  by (simp add: less_eq_mask_iff_take_bit_eq_self shiftr_def take_bit_eq_self_iff_drop_bit_eq_0)

lemma and_mask_eq_iff_shiftr_0:
  "(w AND mask n = w) = (w >> n = 0)"
  for w :: \<open>'a::len word\<close>
  by (simp flip: take_bit_eq_mask add: shiftr_def take_bit_eq_self_iff_drop_bit_eq_0)

lemma mask_shiftl_decompose:
  "mask m << n = mask (m + n) AND NOT (mask n :: 'a::len word)"
  by word_eqI_solve

lemma shiftl_over_and_dist:
  fixes a::"'a::len word"
  shows "(a AND b) << c = (a << c) AND (b << c)"
  by (unfold shiftl_def) (fact push_bit_and)

lemma shiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >> c = (a >> c) AND (b >> c)"
  by (unfold shiftr_def) (fact drop_bit_and)

lemma sshiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >>> c = (a >>> c) AND (b >>> c)"
  by word_eqI

lemma shiftl_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b << c = (a << c) OR (b << c)"
  by (unfold shiftl_def) (fact push_bit_or)

lemma shiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >> c = (a >> c) OR (b >> c)"
  by (unfold shiftr_def) (fact drop_bit_or)

lemma sshiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >>> c = (a >>> c) OR (b >>> c)"
  by word_eqI

lemmas shift_over_ao_dists =
  shiftl_over_or_dist shiftr_over_or_dist
  sshiftr_over_or_dist shiftl_over_and_dist
  shiftr_over_and_dist sshiftr_over_and_dist

lemma shiftl_shiftl:
  fixes a::"'a::len word"
  shows "a << b << c = a << (b + c)"
  by (word_eqI_solve simp: add.commute add.left_commute)

lemma shiftr_shiftr:
  fixes a::"'a::len word"
  shows "a >> b >> c = a >> (b + c)"
  by word_eqI (simp add: add.left_commute add.commute)

lemma shiftl_shiftr1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a << b >> c = a AND (mask (size a - b)) << (b - c)"
  by word_eqI (auto simp: ac_simps)

lemma shiftl_shiftr2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a << b >> c = (a >> (c - b)) AND (mask (size a - c))"
  by word_eqI_solve

lemma shiftr_shiftl1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a >> b << c = (a >> (b - c)) AND (NOT (mask c))"
  by word_eqI_solve

lemma shiftr_shiftl2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a >> b << c = (a << (c - b)) AND (NOT (mask c))"
  by word_eqI (auto simp: ac_simps)

lemmas multi_shift_simps =
  shiftl_shiftl shiftr_shiftr
  shiftl_shiftr1 shiftl_shiftr2
  shiftr_shiftl1 shiftr_shiftl2

lemma shiftr_mask2:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n >> m :: ('a :: len) word) = mask (n - m)"
  by word_eqI_solve

lemma word_shiftl_add_distrib:
  fixes x :: "'a :: len word"
  shows "(x + y) << n = (x << n) + (y << n)"
  by (simp add: shiftl_t2n ring_distribs)

lemma mask_shift:
  "(x AND NOT (mask y)) >> y = x >> y"
  for x :: \<open>'a::len word\<close>
  by word_eqI

lemma shiftr_div_2n':
  "unat (w >> n) = unat w div 2 ^ n"
  by word_eqI

lemma shiftl_shiftr_id:
  "\<lbrakk> n < LENGTH('a); x < 2 ^ (LENGTH('a) - n) \<rbrakk> \<Longrightarrow> x << n >> n = (x::'a::len word)"
  by word_eqI (metis add.commute less_diff_conv)

lemma ucast_shiftl_eq_0:
  fixes w :: "'a :: len word"
  shows "\<lbrakk> n \<ge> LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (w << n) = (0 :: 'b :: len word)"
  by (transfer fixing: n) (simp add: take_bit_push_bit)

lemma word_shift_nonzero:
  fixes x:: "'a::len word"
  assumes "x \<le> 2 ^ m"
      and mn: "m + n < LENGTH('a::len)"
      and "x \<noteq> 0"
    shows "x << n \<noteq> 0"
proof -
  have "0 < unat x"
    by (simp add: assms unat_gt_0)
  moreover
  have "unat x \<le> 2 ^ m"
    by (simp add: assms word_unat_less_le)
  then have \<section>: "2 ^ n * unat x < 2 ^ LENGTH('a)"
    by (metis add_diff_cancel_right' mn le_add2 nat_le_power_trans order_le_less_trans unat_lt2p unat_power_lower)
  ultimately have "0 < 2 ^ n * unat x mod 2 ^ LENGTH('a)"
    by simp
  with \<section> show ?thesis
    by (metis add.commute add_lessD1 less_zeroE mn mult.commute shiftl_eq_mult unat_0 unat_power_lower unat_word_ariths(2))
qed

lemma word_shiftr_lt:
  fixes w :: "'a::len word"
  shows "unat (w >> n) < (2 ^ (LENGTH('a) - n))"
  by (metis mult.commute add_lessD1 div_mod_decomp nat_power_less_diff shiftr_div_2n' unat_lt2p)

lemma shiftr_less_t2n':
  "\<lbrakk> x AND mask (n + m) = x; m < LENGTH('a) \<rbrakk> \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  by (metis and_mask_eq_iff_shiftr_0 eq_mask_less shiftr_shiftr)

lemma shiftr_less_t2n:
  "x < 2 ^ (n + m) \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  by (meson le_add2 less_mask_eq order_le_less_trans p2_gt_0 shiftr_less_t2n' word_gt_a_gt_0)

lemma shiftr_eq_0: "n \<ge> LENGTH('a) \<Longrightarrow> ((w::'a::len word) >> n) = 0"
  by (metis drop_bit_word_beyond shiftr_def)

lemma shiftl_less_t2n:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x < (2 ^ (m - n)); m < LENGTH('a) \<rbrakk> \<Longrightarrow> (x << n) < 2 ^ m"
  by (simp add: shiftl_def take_bit_push_bit word_size flip: mask_eq_iff_w2p take_bit_eq_mask)

lemma shiftl_less_t2n':
  "(x::'a::len word) < 2 ^ m \<Longrightarrow> m+n < LENGTH('a) \<Longrightarrow> x << n < 2 ^ (m + n)"
  by (simp add: shiftl_less_t2n)

lemma scast_bit_test [simp]:
  "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by word_eqI

lemma signed_shift_guard_to_word:
  \<open>unat x * 2 ^ y < 2 ^ n \<longleftrightarrow> x = 0 \<or> x < 1 << n >> y\<close>
    if \<open>n < LENGTH('a)\<close> \<open>0 < n\<close>
    for x :: \<open>'a::len word\<close>
proof (cases \<open>x = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then have \<open>unat x \<noteq> 0\<close>
    by (simp add: unat_eq_0)
  then have \<open>unat x \<ge> 1\<close>
    by simp
  show ?thesis
  proof (cases \<open>y < n\<close>)
    case False
    then have \<open>n \<le> y\<close>
      by simp
    then obtain q where \<open>y = n + q\<close>
      using le_Suc_ex by blast
    moreover have \<open>(2 :: nat) ^ n >> n + q \<le> 1\<close>
      by (simp add: drop_bit_eq_div power_add shiftr_def)
    ultimately show ?thesis
      using \<open>x \<noteq> 0\<close> \<open>unat x \<ge> 1\<close> \<open>n < LENGTH('a)\<close>
      by (simp add: power_add not_less word_le_nat_alt unat_drop_bit_eq shiftr_def shiftl_def)
  next
    case True
    with that have \<open>y < LENGTH('a)\<close>
      by simp
    show ?thesis
    proof (cases \<open>2 ^ n = unat x * 2 ^ y\<close>)
      case True
      moreover have \<open>unat x * 2 ^ y < 2 ^ LENGTH('a)\<close>
        using \<open>n < LENGTH('a)\<close> by (simp flip: True)
      moreover have \<open>(word_of_nat (2 ^ n) :: 'a word) = word_of_nat (unat x * 2 ^ y)\<close>
        using True by simp
      then have \<open>2 ^ n = x * 2 ^ y\<close>
        by simp
      ultimately show ?thesis
        using \<open>y < LENGTH('a)\<close>
        by (auto simp add: drop_bit_eq_div word_less_nat_alt unat_div unat_word_ariths
                           shiftr_def shiftl_def)
    next
      case False
      with \<open>y < n\<close> have *: \<open>unat x \<noteq> 2 ^ n div 2 ^ y\<close>
        by (auto simp flip: power_sub power_add)
      have \<open>unat x * 2 ^ y < 2 ^ n \<longleftrightarrow> unat x * 2 ^ y \<le> 2 ^ n\<close>
        using False by (simp add: less_le)
      also have \<open>\<dots> \<longleftrightarrow> unat x \<le> 2 ^ n div 2 ^ y\<close>
        by (simp add: less_eq_div_iff_mult_less_eq)
      also have \<open>\<dots> \<longleftrightarrow> unat x < 2 ^ n div 2 ^ y\<close>
        using * by (simp add: less_le)
      finally show ?thesis
        using that \<open>x \<noteq> 0\<close>
        by (simp flip: push_bit_eq_mult drop_bit_eq_div
                 add: shiftr_def shiftl_def unat_drop_bit_eq word_less_iff_unsigned [where ?'a = nat])
    qed
  qed
qed

lemma shiftr_not_mask_0:
  "n+m \<ge> LENGTH('a :: len) \<Longrightarrow> ((w::'a::len word) >> n) AND NOT (mask m) = 0"
  by word_eqI

lemma shiftl_mask_is_0[simp]:
  "(x << n) AND mask n = 0"
  for x :: \<open>'a::len word\<close>
  by (simp flip: take_bit_eq_mask add: take_bit_push_bit shiftl_def)

lemma rshift_sub_mask_eq:
  "(a >> (size a - b)) AND mask b = a >> (size a - b)"
  for a :: \<open>'a::len word\<close>
  by (simp add: and_mask_eq_iff_shiftr_0 shiftr_shiftr shiftr_zero_size)

lemma shiftl_shiftr3:
  "b \<le> c \<Longrightarrow> a << b >> c = (a >> c - b) AND mask (size a - c)"
  for a :: \<open>'a::len word\<close>
  by (cases "b = c") (simp_all add: shiftl_shiftr1 shiftl_shiftr2)

lemma and_mask_shiftr_comm:
  "m \<le> size w \<Longrightarrow> (w AND mask m) >> n = (w >> n) AND mask (m-n)"
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask shiftr_shiftr) (simp add: word_size shiftl_shiftr3)

lemma and_mask_shiftl_comm:
  "m+n \<le> size w \<Longrightarrow> (w AND mask m) << n = (w << n) AND mask (m+n)"
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask word_size shiftl_shiftl) (simp add: shiftl_shiftr1)

lemma le_mask_shiftl_le_mask: "s = m + n \<Longrightarrow> x \<le> mask n \<Longrightarrow> x << m \<le> mask s"
  for x :: \<open>'a::len word\<close>
  by (simp add: le_mask_iff shiftl_shiftr3)

lemma word_and_1_shiftl:
  "x AND (1 << n) = (if bit x n then (1 << n) else 0)" for x :: "'a :: len word"
  by word_eqI_solve

lemmas word_and_1_shiftls'
    = word_and_1_shiftl[where n=0]
      word_and_1_shiftl[where n=1]
      word_and_1_shiftl[where n=2]

lemmas word_and_1_shiftls = word_and_1_shiftls' [simplified]

lemma word_and_mask_shiftl:
  "x AND (mask n << m) = ((x >> m) AND mask n) << m"
  for x :: \<open>'a::len word\<close>
  by word_eqI_solve

lemma shift_times_fold:
  "(x :: 'a :: len word) * (2 ^ n) << m = x << (m + n)"
  by (simp add: shiftl_t2n ac_simps power_add)

lemma of_bool_nth:
  "of_bool (bit x v) = (x >> v) AND 1"
  for x :: \<open>'a::len word\<close>
  by (simp add: bit_iff_odd_drop_bit word_and_1 shiftr_def)

lemma shiftr_mask_eq:
  "(x >> n) AND mask (size x - n) = x >> n" for x :: "'a :: len word"
  by (word_eqI_solve dest: test_bit_lenD)

lemma shiftr_mask_eq':
  "m = (size x - n) \<Longrightarrow> (x >> n) AND mask m = x >> n" for x :: "'a :: len word"
  by (simp add: shiftr_mask_eq)

lemma and_eq_0_is_nth:
  fixes x :: "'a :: len word"
  shows "y = 1 << n \<Longrightarrow> ((x AND y) = 0) = (\<not> (bit x n))"
  by (simp add: and_exp_eq_0_iff_not_bit shiftl_def)

lemma word_shift_zero:
  "\<lbrakk> x << n = 0; x \<le> 2^m; m + n < LENGTH('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) = 0"
  using word_shift_nonzero by blast

lemma mask_shift_and_negate[simp]:"(w AND mask n << m) AND NOT (mask n << m) = 0"
  for w :: \<open>'a::len word\<close>
  by word_eqI

(* The seL4 bitfield generator produces functions containing mask and shift operations, such that
 * invoking two of them consecutively can produce something like the following.
 *)
lemma bitfield_op_twice:
  "(x AND NOT (mask n << m) OR ((y AND mask n) << m)) AND NOT (mask n << m) = x AND NOT (mask n << m)"
  for x :: \<open>'a::len word\<close>
  by word_eqI_solve

lemma bitfield_op_twice'':
  "\<lbrakk>NOT a = b << c; \<exists>x. b = mask x\<rbrakk> \<Longrightarrow> (x AND a OR (y AND b << c)) AND a = x AND a"
  for a b :: \<open>'a::len word\<close>
  by word_eqI_solve

lemma shiftr1_unfold: "x div 2 = x >> 1"
  by (simp add: drop_bit_eq_div shiftr_def)

lemma shiftr1_is_div_2: "(x::('a::len) word) >> 1 = x div 2"
  by (simp add: drop_bit_eq_div shiftr_def)

lemma shiftl1_is_mult: "(x << 1) = (x :: 'a::len word) * 2"
  by (metis One_nat_def mult_2 mult_2_right one_add_one
        power_0 power_Suc shiftl_t2n)

lemma shiftr1_lt:"x \<noteq> 0 \<Longrightarrow> (x::('a::len) word) >> 1 < x"
  by (simp add: div_less_dividend_word drop_bit_eq_div shiftr_def)

lemma shiftr1_0_or_1:"(x::('a::len) word) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x = 1"
  by (metis le_mask_iff mask_1 not_less not_less_iff_gr_or_eq word_less_1)

lemma shiftr1_irrelevant_lsb: "bit (x::('a::len) word) 0 \<or> x >> 1 = (x + 1) >> 1"
  by (auto simp: bit_0 shiftr_def drop_bit_Suc ac_simps elim: evenE)

lemma shiftr1_0_imp_only_lsb:"((x::('a::len) word) + 1) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x + 1 = 0"
  by (metis One_nat_def shiftr1_0_or_1 word_less_1 word_overflow)

lemma shiftr1_irrelevant_lsb': "\<not> (bit (x::('a::len) word) 0) \<Longrightarrow> x >> 1 = (x + 1) >> 1"
  using shiftr1_irrelevant_lsb [of x] by simp

(* Perhaps this one should be a simp lemma, but it seems a little dangerous. *)
lemma cast_chunk_assemble_id:
  assumes n: "n = LENGTH('a::len)"
    and "m = LENGTH('b::len)"
    and "n * 2 = m"
  shows "UCAST('a \<rightarrow> 'b) (UCAST('b \<rightarrow> 'a) x::'a word) OR (UCAST('a \<rightarrow> 'b) (UCAST('b \<rightarrow> 'a) (x >> n)::'a word) << n) = x"
proof -
  have "((ucast ((ucast (x >> n))::'a word))::'b word) = x >> n"
    by (metis and_mask_eq_iff_shiftr_0 assms mult_2_right order_refl shiftr_eq_0 shiftr_shiftr ucast_ucast_mask)
  with n show ?thesis
    by (auto simp: ucast_ucast_mask simp flip: and_not_mask word_ao_dist2)
qed

lemma cast_chunk_scast_assemble_id:
  fixes x:: "'b::len word"
  assumes "n = LENGTH('a::len)"
      and "m = LENGTH('b)"
      and "n * 2 = m"
    shows "UCAST('a \<rightarrow> 'b) (SCAST('b \<rightarrow> 'a) x) OR (UCAST('a \<rightarrow> 'b) (SCAST('b \<rightarrow> 'a) (x >> n)) << n) = x"
proof -
  have "SCAST('b \<rightarrow> 'a) x = UCAST('b \<rightarrow> 'a) x"
    by (metis assms down_cast_same is_up is_up_down le_add2 mult_2_right)
  then show ?thesis
    by (metis assms cast_chunk_assemble_id down_cast_same is_down le_add2 mult_2_right)
qed

lemma unat_shiftr_less_t2n:
  fixes x :: "'a :: len word"
  shows "unat x < 2 ^ (n + m) \<Longrightarrow> unat (x >> n) < 2 ^ m"
  by (simp add: shiftr_div_2n' power_add mult.commute less_mult_imp_div_less)

lemma ucast_less_shiftl_helper:
  "\<lbrakk> LENGTH('b) + 2 < LENGTH('a); 2 ^ (LENGTH('b) + 2) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 2) < (n :: 'a::len word)"
  by (meson add_lessD1 order_less_le_trans shiftl_less_t2n' ucast_less)

(* negating a mask which has been shifted to the very left *)
lemma NOT_mask_shifted_lenword:
  "NOT (mask len << (LENGTH('a) - len) ::'a::len word) = mask (LENGTH('a) - len)"
  by word_eqI_solve

(* Comparisons between different word sizes. *)

lemma shiftr_less:
  "(w::'a::len word) < k \<Longrightarrow> w >> n < k"
  by (metis div_le_dividend le_less_trans shiftr_div_2n' unat_arith_simps(2))

lemma word_and_notzeroD:
  "w AND w' \<noteq> 0 \<Longrightarrow> w \<noteq> 0 \<and> w' \<noteq> 0"
  by auto

lemma shiftr_le_0:
  "unat (w::'a::len word) < 2 ^ n \<Longrightarrow> w >> n = (0::'a::len word)"
  by (auto simp add: take_bit_word_eq_self_iff word_less_nat_alt shiftr_def
           simp flip: take_bit_eq_self_iff_drop_bit_eq_0
           intro: ccontr)

lemma of_nat_shiftl:
  "(of_nat x << n) = (of_nat (x * 2 ^ n) :: ('a::len) word)"
proof -
  have "(of_nat x::'a word) << n = of_nat (2 ^ n) * of_nat x"
    using shiftl_t2n by (metis word_unat_power)
  thus ?thesis by simp
qed

lemma shiftl_1_not_0:
  "n < LENGTH('a) \<Longrightarrow> (1::'a::len word) << n \<noteq> 0"
  by (simp add: shiftl_t2n)

(* continue sorting out from here *)

(* usually: x,y = (len_of TYPE ('a)) *)
lemma bitmagic_zeroLast_leq_or1Last:
  "(a::('a::len) word) AND (mask len << x - len) \<le> a OR mask (y - len)"
  by (meson le_word_or2 order_trans word_and_le2)

lemma zero_base_lsb_imp_set_eq_as_bit_operation:
  fixes base ::"'a::len word"
  assumes valid_prefix: "mask (LENGTH('a) - len) AND base = 0"
  shows "(base = NOT (mask (LENGTH('a) - len)) AND a) \<longleftrightarrow>
         (a \<in> {base .. base OR mask (LENGTH('a) - len)})"
proof
  have helper3: "x OR y = x OR y AND NOT x" for x y ::"'a::len word" by (simp add: word_oa_dist2)
  from assms show "base = NOT (mask (LENGTH('a) - len)) AND a \<Longrightarrow>
                    a \<in> {base..base OR mask (LENGTH('a) - len)}"
    by (metis and.commute atLeastAtMost_iff helper3 le_word_or2 or.commute word_and_le1)
next
  assume "a \<in> {base..base OR mask (LENGTH('a) - len)}"
  hence a: "base \<le> a \<and> a \<le> base OR mask (LENGTH('a) - len)" by simp
  show "base = NOT (mask (LENGTH('a) - len)) AND a"
  proof -
    have f2: "\<forall>x\<^sub>0. base AND NOT (mask x\<^sub>0) \<le> a AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f3: "\<forall>x\<^sub>0. a AND NOT (mask x\<^sub>0) \<le> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f4: "base = base AND NOT (mask (LENGTH('a) - len))"
      using valid_prefix by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f5: "\<forall>x\<^sub>6. (base OR x\<^sub>6) AND NOT (mask (LENGTH('a) - len)) =
                      base OR x\<^sub>6 AND NOT (mask (LENGTH('a) - len))"
      using word_ao_dist by (metis)
    have f6: "\<forall>x\<^sub>2 x\<^sub>3. a AND NOT (mask x\<^sub>2) \<le> x\<^sub>3 \<or>
                      \<not> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>2) \<le> x\<^sub>3"
      using f3 dual_order.trans by auto
    have "base = (base OR mask (LENGTH('a) - len)) AND NOT (mask (LENGTH('a) - len))"
      using f5 by auto
    hence "base = a AND NOT (mask (LENGTH('a) - len))"
      using f2 f4 f6 by (metis eq_iff)
    thus "base = NOT (mask (LENGTH('a) - len)) AND a"
      by (metis word_bw_comms(1))
  qed
qed

lemma of_nat_eq_signed_scast:
  "(of_nat x = (y :: ('a::len) signed word))
   = (of_nat x = (scast y :: 'a word))"
  by (metis scast_of_nat scast_scast_id(2))

lemma word_aligned_add_no_wrap_bounded:
  "\<lbrakk> w + 2^n \<le> x; w + 2^n \<noteq> 0; is_aligned w n \<rbrakk> \<Longrightarrow> (w::'a::len word) < x"
  by (blast dest: is_aligned_no_overflow le_less_trans word_leq_le_minus_one)

lemma mask_Suc:
  "mask (Suc n) = (2 :: 'a::len word) ^ n + mask n"
  by (simp add: mask_eq_decr_exp)

lemma mask_mono:
  "sz' \<le> sz \<Longrightarrow> mask sz' \<le> (mask sz :: 'a::len word)"
  by (simp add: le_mask_iff shiftr_mask_le)

lemma aligned_mask_disjoint:
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; b \<le> mask n \<rbrakk> \<Longrightarrow> a AND b = 0"
  by (metis and_zero_eq is_aligned_mask le_mask_imp_and_mask word_bw_lcs(1))

lemma word_and_or_mask_aligned:
  "\<lbrakk> is_aligned a n; b \<le> mask n \<rbrakk> \<Longrightarrow> a + b = a OR b"
  by (simp add: aligned_mask_disjoint word_plus_and_or_coroll)

lemma word_and_or_mask_aligned2:
  \<open>is_aligned b n \<Longrightarrow> a \<le> mask n \<Longrightarrow> a + b = a OR b\<close>
  using word_and_or_mask_aligned [of b n a] by (simp add: ac_simps)

lemma is_aligned_ucastI:
  "is_aligned w n \<Longrightarrow> is_aligned (ucast w) n"
  by (simp add: bit_ucast_iff is_aligned_nth)

lemma ucast_le_maskI:
  "a \<le> mask n \<Longrightarrow> UCAST('a::len \<rightarrow> 'b::len) a \<le> mask n"
  by (metis and_mask_eq_iff_le_mask ucast_and_mask)

lemma ucast_add_mask_aligned:
  "\<lbrakk> a \<le> mask n; is_aligned b n \<rbrakk> \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) (a + b) = ucast a + ucast b"
  by (metis add.commute is_aligned_ucastI ucast_le_maskI ucast_or_distrib word_and_or_mask_aligned)

lemma ucast_shiftl:
  "LENGTH('b) \<le> LENGTH ('a) \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) x << n = ucast (x << n)"
  by word_eqI_solve

lemma ucast_leq_mask:
  "LENGTH('a) \<le> n \<Longrightarrow> ucast (x::'a::len word) \<le> mask n"
  by (metis and_mask_eq_iff_le_mask ucast_and_mask ucast_id ucast_mask_drop)

lemma shiftl_inj:
  \<open>x = y\<close>
    if \<open>x << n = y << n\<close> \<open>x \<le> mask (LENGTH('a) - n)\<close> \<open>y \<le> mask (LENGTH('a) - n)\<close>
    for x y :: \<open>'a::len word\<close>
proof (cases \<open>n < LENGTH('a)\<close>)
  case False
  with that show ?thesis
    by simp
next
  case True
  moreover from that have \<open>take_bit (LENGTH('a) - n) x = x\<close> \<open>take_bit (LENGTH('a) - n) y = y\<close>
    by (simp_all add: less_eq_mask_iff_take_bit_eq_self)
  ultimately show ?thesis
    using \<open>x << n = y << n\<close> by (metis diff_less gr_implies_not0 linorder_cases linorder_not_le shiftl_shiftr_id shiftl_x_0 take_bit_word_eq_self_iff)
qed

lemma distinct_word_add_ucast_shift_inj:
  \<open>p' = p \<and> off' = off\<close>
  if *: \<open>p + (UCAST('a::len \<rightarrow> 'b::len) off << n) = p' + (ucast off' << n)\<close>
    and \<open>is_aligned p n'\<close> \<open>is_aligned p' n'\<close> \<open>n' = n + LENGTH('a)\<close> \<open>n' < LENGTH('b)\<close>
proof -
  from \<open>n' = n + LENGTH('a)\<close>
  have [simp]: \<open>n' - n = LENGTH('a)\<close> \<open>n + LENGTH('a) = n'\<close>
    by simp_all
  from \<open>is_aligned p n'\<close> obtain q
    where p: \<open>p = push_bit n' (word_of_nat q)\<close> \<open>q < 2 ^ (LENGTH('b) - n')\<close>
    by (rule is_alignedE')
  from \<open>is_aligned p' n'\<close> obtain q'
    where p': \<open>p' = push_bit n' (word_of_nat q')\<close> \<open>q' < 2 ^ (LENGTH('b) - n')\<close>
    by (rule is_alignedE')
  define m :: nat where \<open>m = unat off\<close>
  then have off: \<open>off = word_of_nat m\<close>
    by simp
  define m' :: nat where \<open>m' = unat off'\<close>
  then have off': \<open>off' = word_of_nat m'\<close>
    by simp
  have \<open>push_bit n' q + take_bit n' (push_bit n m) < 2 ^ LENGTH('b)\<close>
    by (metis id_apply is_aligned_no_wrap''' of_nat_eq_id of_nat_push_bit p(1) p(2) take_bit_nat_eq_self_iff take_bit_nat_less_exp take_bit_push_bit that(2) that(5) unsigned_of_nat)
  moreover have \<open>push_bit n' q' + take_bit n' (push_bit n m') < 2 ^ LENGTH('b)\<close>
    by (metis \<open>n' - n = LENGTH('a)\<close> id_apply is_aligned_no_wrap''' m'_def of_nat_eq_id of_nat_push_bit off' p'(1) p'(2) take_bit_nat_eq_self_iff take_bit_push_bit that(3) that(5) unsigned_of_nat)
  ultimately have \<open>push_bit n' q + take_bit n' (push_bit n m) = push_bit n' q' + take_bit n' (push_bit n m')\<close>
    using * by (simp add: p p' off off' push_bit_of_nat push_bit_take_bit word_of_nat_inj unsigned_of_nat shiftl_def flip: of_nat_add)
  then have \<open>int (push_bit n' q + take_bit n' (push_bit n m))
    = int (push_bit n' q' + take_bit n' (push_bit n m'))\<close>
    by simp
  then have \<open>concat_bit n' (int (push_bit n m)) (int q)
    = concat_bit n' (int (push_bit n m')) (int q')\<close>
    by (simp add: of_nat_push_bit of_nat_take_bit concat_bit_eq)
  then show ?thesis
    by (simp add: p p' off off' take_bit_of_nat take_bit_push_bit word_of_nat_eq_iff concat_bit_eq_iff)
      (simp add: push_bit_eq_mult)
qed

lemma word_upto_Nil:
  "y < x \<Longrightarrow> [x .e. y ::'a::len word] = []"
  by (simp add: upto_enum_red not_le word_less_nat_alt)

lemma word_enum_decomp_elem:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y"
proof -
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    using assms by (auto dest: arg_cong[where f=set])
  then show ?thesis by auto
qed

lemma word_enum_prefix:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> as = (if x < a then [x .e. a - 1] else [])"
proof (induction as arbitrary: x)
  case Nil
  show ?case
  proof (cases "x < y")
    case True
    then show ?thesis
      using local.Nil word_upto_Cons_eq by force
  next
    case False
    then show ?thesis
      using local.Nil not_less_iff_gr_or_eq word_upto_Nil by fastforce
  qed
next
  case (Cons b as)
  show ?case
  proof (cases x y rule: linorder_cases)
    case less
    with Cons.prems have "b + 1 \<le> a"
      using word_enum_decomp_elem word_upto_Cons_eq by fastforce
    moreover have "x + 1 \<le> a"
      using Cons.prems less word_enum_decomp_elem word_upto_Cons_eq by fastforce
    moreover have "(x + 1 \<le> a) = (x < a)"
      by (metis less word_Suc_le word_not_simps(3))
    ultimately
    show ?thesis
      using Cons less word_l_diffs(2) less_is_non_zero_p1 olen_add_eqv unat_plus_simple
        word_overflow_unat word_upto_Cons_eq by fastforce
  next
    case equal
    then show ?thesis
      using Cons.prems by auto
  next
    case greater
    then show ?thesis
      using Cons
      by (simp add: word_upto_Nil)
  qed
qed

lemma word_enum_decomp_set:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> a \<notin> set as"
  by (metis distinct_append distinct_enum_upto' not_distinct_conv_prefix)

lemma word_enum_decomp:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y \<and> a \<notin> set as \<and> (\<forall>z \<in> set as. x \<le> z \<and> z \<le> y)"
proof -
  from assms
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    by (auto dest: arg_cong[where f=set])
  with word_enum_decomp_set[OF assms]
  show ?thesis by auto
qed

lemma of_nat_unat_le_mask_ucast:
  "\<lbrakk>of_nat (unat t) = w; t \<le> mask LENGTH('a)\<rbrakk> \<Longrightarrow> t = UCAST('a::len \<rightarrow> 'b::len) w"
  by (clarsimp simp: ucast_nat_def ucast_ucast_mask simp flip: and_mask_eq_iff_le_mask)

lemma less_diff_gt0:
  "a < b \<Longrightarrow> (0 :: 'a :: len word) < b - a"
  by unat_arith

lemma unat_plus_gt:
  "unat ((a :: 'a :: len word) + b) \<le> unat a + unat b"
  by (clarsimp simp: unat_plus_if_size)

lemma const_less:
  "\<lbrakk> (a :: 'a :: len word) - 1 < b; a \<noteq> b \<rbrakk> \<Longrightarrow> a < b"
  by (metis less_1_simp word_le_less_eq)

lemma add_mult_aligned_neg_mask:
  \<open>(x + y * m) AND NOT(mask n) = (x AND NOT(mask n)) + y * m\<close>
  if \<open>m AND (2 ^ n - 1) = 0\<close>
  for x y m :: \<open>'a::len word\<close>
  by (metis (no_types, opaque_lifting)
            add.assoc add.commute add.right_neutral add_uminus_conv_diff
            mask_eq_decr_exp mask_eqs(2) mask_eqs(6) mult.commute mult_zero_left
            subtract_mask(1) that)

lemma unat_of_nat_minus_1:
  "\<lbrakk> n < 2 ^ LENGTH('a); n \<noteq> 0 \<rbrakk> \<Longrightarrow> unat ((of_nat n:: 'a :: len word) - 1) = n - 1"
  by (simp add: of_nat_diff unat_eq_of_nat)

lemma word_eq_zeroI:
  "a \<le> a - 1 \<Longrightarrow> a = 0" for a :: "'a :: len word"
  by (simp add: word_must_wrap)

lemma word_add_format:
  "(-1 :: 'a :: len  word) + b + c = b + (c - 1)"
  by simp

lemma upto_enum_word_nth:
  assumes "i \<le> j" and "k \<le> unat (j - i)"
  shows "[i .e. j] ! k = i + of_nat k"
proof -
  have "unat i + unat (j-i) < 2 ^ LENGTH('a)"
    by (metis add.commute \<open>i \<le> j\<close> eq_diff_eq no_olen_add_nat)
  then have "toEnum (unat i + k) = i + word_of_nat k"
    using assms by auto
  moreover have "[j] ! (k + unat i - unat j) = i + word_of_nat k"
    if "\<not> k < unat j - unat i"  "unat i \<le> unat j"
    using that assms unat_sub by fastforce
  moreover have "[] ! k = i + word_of_nat k" if "\<not> unat i \<le> unat j"
    using that \<open>i \<le> j\<close> word_less_eq_iff_unsigned by blast
  ultimately show ?thesis
    by (auto simp: upto_enum_def nth_append)
qed

lemma upto_enum_step_nth:
  "\<lbrakk> a \<le> c; n \<le> unat ((c - a) div (b - a)) \<rbrakk>
   \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  by (clarsimp simp: upto_enum_step_def not_less[symmetric] upto_enum_word_nth)

lemma upto_enum_inc_1_len:
  fixes a :: "'a::len word"
  assumes "a < - 1"
  shows "[(0 :: 'a :: len word) .e. 1 + a] = [0 .e. a] @ [1 + a]"
proof -
  have "unat (1+a) = 1 + unat a"
    by (simp add: add_eq_0_iff assms unatSuc word_order.not_eq_extremum)
  with assms show ?thesis
    by (simp add: upto_enum_word)
qed

lemma neg_mask_add:
  "y AND mask n = 0 \<Longrightarrow> x + y AND NOT(mask n) = (x AND NOT(mask n)) + y"
  for x y :: \<open>'a::len word\<close>
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma shiftr_shiftl_shiftr[simp]:
  "(x :: 'a :: len word) >> a << a >> a = x >> a"
  by (word_eqI_solve dest: bit_imp_le_length)

lemma add_right_shift:
  fixes x y :: \<open>'a::len word\<close>
  assumes "x AND mask n = 0" and "y AND mask n = 0" and "x \<le> x + y"
  shows "(x + y) >> n = (x >> n) + (y >> n)"
proof -
  obtain \<section>: "is_aligned x n" "is_aligned y n" "unat x + unat y < 2 ^ LENGTH('a)"
    using assms is_aligned_mask no_olen_add_nat by blast
  then have "unat x div 2 ^ n + unat y div 2 ^ n < 2 ^ LENGTH('a)"
    by (metis add_le_mono add_lessD1 div_le_dividend le_Suc_ex)
  with \<section> show ?thesis
    by (metis (no_types, lifting) div_add is_aligned_iff_dvd_nat shiftr_div_2n' unat_plus_if' word_unat_eq_iff)
qed

lemma sub_right_shift:
  "\<lbrakk> x AND mask n = 0; y AND mask n = 0; y \<le> x \<rbrakk>
   \<Longrightarrow> (x - y) >> n = (x >> n :: 'a :: len word) - (y >> n)"
  by (smt (verit) add_diff_cancel_left' add_right_shift diff_0_right diff_add_cancel mask_eqs(4))

lemma and_and_mask_simple:
  "y AND mask n = mask n \<Longrightarrow> (x AND y) AND mask n = x AND mask n"
  by (simp add: ac_simps)

lemma and_and_mask_simple_not:
  "y AND mask n = 0 \<Longrightarrow> (x AND y) AND mask n = 0"
  by (simp add: ac_simps)

lemma word_and_le':
  "b \<le> c \<Longrightarrow> (a :: 'a :: len word) AND b \<le> c"
  by (metis word_and_le1 order_trans)

lemma word_and_less':
  "b < c \<Longrightarrow> (a :: 'a :: len word) AND b < c"
  by transfer simp

lemma shiftr_w2p:
  "x < LENGTH('a) \<Longrightarrow> 2 ^ x = (2 ^ (LENGTH('a) - 1) >> (LENGTH('a) - 1 - x) :: 'a :: len word)"
  by word_eqI_solve

lemma t2p_shiftr:
  "\<lbrakk> b \<le> a; a < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ a >> b = 2 ^ (a - b)"
  by word_eqI_solve

lemma scast_1[simp]:
  "scast (1 :: 'a :: len signed word) = (1 :: 'a word)"
  by simp

lemma unsigned_uminus1 [simp]:
  \<open>(unsigned (-1::'b::len word)::'c::len word) = mask LENGTH('b)\<close>
  by (fact unsigned_minus_1_eq_mask)

lemma ucast_ucast_mask_eq:
  "\<lbrakk> UCAST('a::len \<rightarrow> 'b::len) x = y; x AND mask LENGTH('b) = x \<rbrakk> \<Longrightarrow> x = ucast y"
  by (drule sym) (simp flip: take_bit_eq_mask add: unsigned_ucast_eq)

lemma ucast_up_eq:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> LENGTH ('b) \<rbrakk>
   \<Longrightarrow> ucast x = (ucast y::'a::len word)"
  by (simp add: word_eq_iff bit_simps)

lemma ucast_up_neq:
  "\<lbrakk> ucast x \<noteq> (ucast y::'b::len word); LENGTH('b) \<le> LENGTH ('a) \<rbrakk>
   \<Longrightarrow> ucast x \<noteq> (ucast y::'a::len word)"
  by (fastforce dest: ucast_up_eq)

lemma mask_AND_less_0:
  "\<lbrakk> x AND mask n = 0; m \<le> n \<rbrakk> \<Longrightarrow> x AND mask m = 0"
  for x :: \<open>'a::len word\<close>
  by (metis mask_twice2 word_and_notzeroD)

lemma mask_len_id:
  "(x :: 'a :: len word) AND mask LENGTH('a) = x"
  by simp

lemma scast_ucast_down_same:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> SCAST('a \<rightarrow> 'b) = UCAST('a::len \<rightarrow> 'b::len)"
  by (simp add: down_cast_same is_down)

lemma word_aligned_0_sum:
  "\<lbrakk> a + b = 0; is_aligned (a :: 'a :: len word) n; b \<le> mask n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> a = 0 \<and> b = 0"
  by (simp add: word_plus_and_or_coroll aligned_mask_disjoint word_or_zero)

lemma mask_eq1_nochoice:
  "\<lbrakk> LENGTH('a) > 1; (x :: 'a :: len word) AND 1 = x \<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  by (metis word_and_1)

lemma shiftr_and_eq_shiftl:
  "(w >> n) AND x = y \<Longrightarrow> w AND (x << n) = (y << n)" for y :: "'a:: len word"
  by (smt (verit, best) and_not_mask mask_eq_0_eq_x shiftl_mask_is_0 shiftl_over_and_dist word_bw_lcs(1))

lemma add_mask_lower_bits':
  "\<lbrakk> len = LENGTH('a); is_aligned (x :: 'a :: len word) n;
     \<forall>n' \<ge> n. n' < len \<longrightarrow> \<not> bit p n' \<rbrakk>
   \<Longrightarrow> x + p AND NOT(mask n) = x"
  using add_mask_lower_bits by auto

lemma leq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) \<le> mask high_bits"
  by (simp add: le_mask_iff shiftr_shiftr ac_simps)

lemma ucast_ucast_eq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + LENGTH('b))
   \<Longrightarrow> ucast((ucast (x >> low_bits)) :: 'b :: len word) = x >> low_bits"
  by (simp add: and_mask_eq_iff_le_mask leq_mask_shift ucast_ucast_mask)

lemma const_le_unat:
  "\<lbrakk> b < 2 ^ LENGTH('a); of_nat b \<le> a \<rbrakk> \<Longrightarrow> b \<le> unat (a :: 'a :: len word)"
  by (simp add: word_le_nat_alt unsigned_of_nat take_bit_nat_eq_self)

lemma upt_enum_offset_trivial:
  "\<lbrakk> x < 2 ^ LENGTH('a) - 1 ; n \<le> unat x \<rbrakk>
   \<Longrightarrow> ([(0 :: 'a :: len word) .e. x] ! n) = of_nat n"
  by (induct x arbitrary: n) (auto simp: upto_enum_word_nth)

lemma word_le_mask_out_plus_2sz:
  "x \<le> (x AND NOT(mask sz)) + 2 ^ sz - 1"
  for x :: \<open>'a::len word\<close>
  by (metis add_diff_eq word_neg_and_le)

lemma ucast_add:
  "ucast (a + (b :: 'a :: len word)) = ucast a + (ucast b :: ('a signed word))"
  by transfer (simp add: take_bit_add)

lemma ucast_minus:
  "ucast (a - (b :: 'a :: len word)) = ucast a - (ucast b :: ('a signed word))"
  by (metis (no_types, opaque_lifting) add_diff_cancel_left' add_diff_eq ucast_add)

lemma scast_ucast_add_one [simp]:
  "scast (ucast (x :: 'a::len word) + (1 :: 'a signed word)) = x + 1"
  by (metis scast_ucast_id ucast_1 ucast_add)

lemma word_and_le_plus_one:
  "a > 0 \<Longrightarrow> (x :: 'a :: len word) AND (a - 1) < a"
  by (simp add: gt0_iff_gem1 word_and_less')

lemma unat_of_ucast_then_shift_eq_unat_of_shift[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) >> n) = unat (x >> n)"
  by (simp add: shiftr_div_2n' unat_ucast_up_simp)

lemma unat_of_ucast_then_mask_eq_unat_of_mask[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) AND mask m) = unat (x AND mask m)"
  by (metis ucast_and_mask unat_ucast_up_simp)

lemma shiftr_less_t2n3:
  "\<lbrakk> (2 :: 'a word) ^ (n + m) = 0; m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x :: 'a :: len word) >> n < 2 ^ m"
  by (fastforce intro: shiftr_less_t2n' simp: mask_eq_decr_exp power_overflow)

lemma unat_shiftr_le_bound:
  "\<lbrakk> 2 ^ (LENGTH('a :: len) - n) - 1 \<le> bnd; 0 < n \<rbrakk>
   \<Longrightarrow> unat ((x :: 'a word) >> n) \<le> bnd"
  by (metis add.commute le_diff_conv less_Suc_eq_le order_less_le_trans plus_1_eq_Suc word_shiftr_lt)

lemma shiftr_eqD:
  "\<lbrakk> x >> n = y >> n; is_aligned x n; is_aligned y n \<rbrakk>
   \<Longrightarrow> x = y"
  by (metis is_aligned_shiftr_shiftl)

lemma word_shiftr_shiftl_shiftr_eq_shiftr:
  "a \<ge> b \<Longrightarrow> (x :: 'a :: len word) >> a << b >> b = x >> a"
  by (simp add: mask_shift shiftr_shiftl1 shiftr_shiftr)

lemma of_int_uint_ucast:
   "of_int (uint (x :: 'a::len word)) = (ucast x :: 'b::len word)"
  by (fact Word.of_int_uint)

lemma mod_mask_drop:
  "\<lbrakk> m = 2 ^ n; 0 < m; mask n AND msk = mask n \<rbrakk>
   \<Longrightarrow> (x mod m) AND msk = x mod m"
  for x :: \<open>'a::len word\<close>
  by (simp add: word_mod_2p_is_mask word_bw_assocs)

lemma mask_eq_ucast_eq:
  "\<lbrakk> x AND mask LENGTH('a) = (x :: ('c :: len word));
     LENGTH('a) \<le> LENGTH('b)\<rbrakk>
    \<Longrightarrow> ucast (ucast x :: ('a :: len word)) = (ucast x :: ('b :: len word))"
  by (metis ucast_and_mask ucast_id ucast_ucast_mask ucast_up_eq)

lemma of_nat_less_t2n:
  "of_nat i < (2 :: ('a :: len) word) ^ n \<Longrightarrow> n < LENGTH('a) \<and> unat (of_nat i :: 'a word) < 2 ^ n"
  by (metis order_less_trans p2_gt_0 unat_less_power word_neq_0_conv)

lemma two_power_increasing_less_1:
  "\<lbrakk> n \<le> m; m \<le> LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n - 1 \<le> 2 ^ m - 1"
  by (meson le_m1_iff_lt order_le_less_trans p2_gt_0 two_power_increasing word_1_le_power word_le_minus_mono_left)

lemma word_sub_mono4:
  "\<lbrakk> y + x \<le> z + x; y \<le> y + x; z \<le> z + x \<rbrakk> \<Longrightarrow> y \<le> z" for y :: "'a :: len word"
  by (simp add: word_add_le_iff2)

lemma eq_or_less_helperD:
  "\<lbrakk> n = unat (2 ^ m - 1 :: 'a :: len word) \<or> n < unat (2 ^ m - 1 :: 'a word); m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> n < 2 ^ m"
  by (meson le_less_trans nat_less_le unat_less_power word_power_less_1)

lemma mask_sub:
  "n \<le> m \<Longrightarrow> mask m - mask n = mask m AND NOT(mask n :: 'a::len word)"
  by (metis (full_types) and_mask_eq_iff_shiftr_0 mask_out_sub_mask shiftr_mask_le word_bw_comms(1))

lemma neg_mask_diff_bound:
  "sz'\<le> sz \<Longrightarrow> (ptr AND NOT(mask sz')) - (ptr AND NOT(mask sz)) \<le> 2 ^ sz - 2 ^ sz'"
  (is "_ \<Longrightarrow> ?lhs \<le> ?rhs")
  for ptr :: \<open>'a::len word\<close>
proof -
  assume lt: "sz' \<le> sz"
  hence "?lhs = ptr AND (mask sz AND NOT(mask sz'))"
    by (metis add_diff_cancel_left' multiple_mask_trivia)
  also have "\<dots> \<le> ?rhs" using lt
    by (metis (mono_tags) add_diff_eq diff_eq_eq eq_iff mask_2pm1 mask_sub word_and_le')
  finally show ?thesis by simp
qed

lemma mask_out_eq_0:
  "\<lbrakk> idx < 2 ^ sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow> (of_nat idx :: 'a :: len word) AND NOT(mask sz) = 0"
  by (simp add: of_nat_power less_mask_eq mask_eq_0_eq_x)

lemma is_aligned_neg_mask_eq':
  "is_aligned ptr sz = (ptr AND NOT(mask sz) = ptr)"
  using is_aligned_mask mask_eq_0_eq_x by blast

lemma neg_mask_mask_unat:
  "sz < LENGTH('a)
   \<Longrightarrow> unat ((ptr :: 'a :: len word) AND NOT(mask sz)) + unat (ptr AND mask sz) = unat ptr"
  by (metis AND_NOT_mask_plus_AND_mask_eq unat_plus_simple word_and_le2)

lemma unat_pow_le_intro:
  "LENGTH('a) \<le> n \<Longrightarrow> unat (x :: 'a :: len word) < 2 ^ n"
  by (metis lt2p_lem not_le of_nat_le_iff of_nat_numeral semiring_1_class.of_nat_power uint_nat)

lemma unat_shiftl_less_t2n:
  \<open>unat (x << n) < 2 ^ m\<close>
  if \<open>unat (x :: 'a :: len word) < 2 ^ (m - n)\<close> \<open>m < LENGTH('a)\<close>
proof (cases \<open>n \<le> m\<close>)
  case False
  with that show ?thesis
    by (simp add: unsigned_eq_0_iff)
next
  case True
  moreover define q r where \<open>q = m - n\<close> and \<open>r = LENGTH('a) - n - q\<close>
  ultimately have \<open>m - n = q\<close> \<open>m = n + q\<close> \<open>LENGTH('a) = r + q + n\<close>
    using that by simp_all
  with that show ?thesis
    by (metis le_add2 order_le_less_trans shiftl_less_t2n unat_power_lower word_less_iff_unsigned)
qed

lemma unat_is_aligned_add:
  "\<lbrakk> is_aligned p n; unat d < 2 ^ n \<rbrakk>
   \<Longrightarrow> unat (p + d AND mask n) = unat d \<and> unat (p + d AND NOT(mask n)) = unat p"
  by (metis add_diff_cancel_left' add_mask_lower_bits is_aligned_add_helper order_le_less_trans
       subtract_mask(2) unat_power_lower word_less_nat_alt)

lemma unat_shiftr_shiftl_mask_zero:
  "\<lbrakk> c + a \<ge> LENGTH('a) + b ; c < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (((q :: 'a :: len word) >> a << b) AND NOT(mask c)) = 0"
  by (fastforce intro: unat_is_aligned_add[where p=0 and n=c, simplified, THEN conjunct2]
                       unat_shiftl_less_t2n unat_shiftr_less_t2n unat_pow_le_intro)

lemmas of_nat_ucast = ucast_of_nat[symmetric]

lemma shift_then_mask_eq_shift_low_bits:
  "x \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) AND mask high_bits = x >> low_bits"
  for x :: \<open>'a::len word\<close>
  by (simp add: leq_mask_shift le_mask_imp_and_mask)

lemma leq_low_bits_iff_zero:
  "\<lbrakk> x \<le> mask (low bits + high bits); x >> low_bits = 0 \<rbrakk> \<Longrightarrow> (x AND mask low_bits = 0) = (x = 0)"
  for x :: \<open>'a::len word\<close>
  using and_mask_eq_iff_shiftr_0 by force

lemma unat_less_iff:
  "\<lbrakk> unat (a :: 'a :: len word) = b; c < 2 ^ LENGTH('a) \<rbrakk> \<Longrightarrow> (a < of_nat c) = (b < c)"
  using unat_ucast_less_no_overflow_simp by blast

lemma is_aligned_no_overflow3:
 "\<lbrakk> is_aligned (a :: 'a :: len word) n; n < LENGTH('a); b < 2 ^ n; c \<le> 2 ^ n; b < c \<rbrakk>
  \<Longrightarrow> a + b \<le> a + (c - 1)"
  by (meson is_aligned_no_wrap' le_m1_iff_lt not_le word_less_sub_1 word_plus_mono_right)

lemma mask_add_aligned_right:
  "is_aligned p n \<Longrightarrow> (q + p) AND mask n = q AND mask n"
  by (simp add: mask_add_aligned add.commute)

lemma leq_high_bits_shiftr_low_bits_leq_bits_mask:
  "x \<le> mask high_bits \<Longrightarrow> (x :: 'a :: len word) << low_bits \<le> mask (low_bits + high_bits)"
  by (metis le_mask_shiftl_le_mask)

lemma word_two_power_neg_ineq:
  assumes "2 ^ m \<noteq> (0::'a word)"
  shows "2 ^ n \<le> - (2 ^ m :: 'a :: len word)"
proof (cases "n < LENGTH('a) \<and> m < LENGTH('a)")
  case True
  with assms show ?thesis
  by (metis bit_minus_exp_iff linorder_not_le nat_less_le nth_bounded possible_bit_word)
next
  case False
  with assms show ?thesis
    by (force simp: power_overflow)
qed

lemma unat_shiftl_absorb:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<le> 2 ^ p; p + k < LENGTH('a) \<rbrakk> \<Longrightarrow> unat x * 2 ^ k = unat (x * 2 ^ k)"
  by (smt (verit) add_diff_cancel_right' add_lessD1 le_add2 le_less_trans mult.commute nat_le_power_trans
          unat_lt2p unat_mult_lem unat_power_lower word_le_nat_alt)

lemma word_plus_mono_right_split:
  fixes x :: "'a :: len word"
  assumes "unat (x AND mask sz) + unat z < 2 ^ sz" and "sz < LENGTH('a)"
  shows "x \<le> x + z"
proof -
  have *: "is_aligned (x AND NOT (mask sz)) sz" "word_of_nat (unat z) = z"
          "word_of_nat (unat (x AND mask sz)) = x AND mask sz"
    by auto
  with assms have "x AND mask sz \<le> (x AND mask sz) + z"
    by (metis (mono_tags, lifting) le_unat_uoi of_nat_add order_less_imp_le unat_plus_simple unat_power_lower)
  then have "(x AND NOT(mask sz)) + (x AND mask sz) \<le> (x AND NOT(mask sz)) + ((x AND mask sz) + z)"
    by (metis (no_types, lifting) of_nat_power assms * is_aligned_no_wrap' of_nat_add word_plus_mono_right)
  then show ?thesis
    by (simp add: and_not_eq_minus_and)
qed

lemma mul_not_mask_eq_neg_shiftl:
  "NOT(mask n :: 'a::len word) = -1 << n"
  by (simp add: NOT_mask shiftl_t2n)

lemma shiftr_mul_not_mask_eq_and_not_mask:
  "(x >> n) * NOT(mask n) = - (x AND NOT(mask n))"
  for x :: \<open>'a::len word\<close>
  by (metis NOT_mask and_not_mask mult_minus_left mult.commute shiftl_t2n)

lemma mask_eq_n1_shiftr:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n :: 'a :: len word) = -1 >> (LENGTH('a) - n)"
  by (metis diff_diff_cancel eq_refl mask_full shiftr_mask2)

lemma is_aligned_mask_out_add_eq:
  "is_aligned p n \<Longrightarrow> (p + x) AND NOT(mask n) = p + (x AND NOT(mask n))"
  by (simp add: mask_out_add_aligned)

lemmas is_aligned_mask_out_add_eq_sub
    = is_aligned_mask_out_add_eq[where x="a - b" for a b, simplified field_simps]

lemma aligned_bump_down:
  "is_aligned x n \<Longrightarrow> (x - 1) AND NOT(mask n) = x - 2 ^ n"
  by (drule is_aligned_mask_out_add_eq[where x="-1"]) (simp add: NOT_mask)

lemma unat_2tp_if:
  "unat (2 ^ n :: ('a :: len) word) = (if n < LENGTH ('a) then 2 ^ n else 0)"
  by (simp add: unsigned_eq_0_iff)

lemma mask_of_mask:
  "mask (n::nat) AND mask (m::nat) = (mask (min m n) :: 'a::len word)"
  by word_eqI_solve

lemma unat_signed_ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> unat (ucast (x :: 'a :: len word) :: 'b :: len signed word) = unat x"
  by (simp add: unat_ucast_up_simp)

lemma toEnum_of_ucast:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow>
   (toEnum (unat (b::'b :: len word))::'a :: len word) = of_nat (unat b)"
  by (simp add: unat_pow_le_intro)

lemma plus_mask_AND_NOT_mask_eq:
  "x AND NOT(mask n) = x \<Longrightarrow> (x + mask n) AND NOT(mask n) = x" for x::\<open>'a::len word\<close>
  by (metis AND_NOT_mask_plus_AND_mask_eq is_aligned_neg_mask2 mask_AND_NOT_mask mask_out_add_aligned word_and_not)

lemmas unat_ucast_mask = unat_ucast_eq_unat_and_mask[where w=a for a]

lemma t2n_mask_eq_if:
  "2 ^ n AND mask m = (if n < m then 2 ^ n else (0 :: 'a::len word))"
  by word_eqI_solve

lemma unat_ucast_le:
  "unat (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> unat x"
  by (simp add: ucast_nat_def word_unat_less_le)

lemma ucast_le_up_down_iff:
  "\<lbrakk> LENGTH('a) \<le> LENGTH('b); (x :: 'b :: len word) \<le> ucast (- 1 :: 'a :: len word) \<rbrakk>
   \<Longrightarrow> (ucast x \<le> (y :: 'a word)) = (x \<le> ucast y)"
  using le_max_word_ucast_id ucast_le_ucast by metis

lemma ucast_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> ucast (ucast (p AND mask a >> b) :: 'a :: len word) = p AND mask a >> b"
  by (simp add: mask_mono ucast_ucast_eq_mask_shift word_and_le')

lemma unat_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> unat (ucast (p AND mask a >> b) :: 'a :: len word) = unat (p AND mask a >> b)"
  by (metis linear ucast_ucast_mask_shift unat_ucast_up_simp)

lemma mask_overlap_zero:
  "a \<le> b \<Longrightarrow> (p AND mask a) AND NOT(mask b) = 0"
  for p :: \<open>'a::len word\<close>
  by (metis NOT_mask_AND_mask mask_lower_twice2 max_def)

lemma mask_shifl_overlap_zero:
  "a + c \<le> b \<Longrightarrow> (p AND mask a << c) AND NOT(mask b) = 0"
  for p :: \<open>'a::len word\<close>
  by (metis and_mask_0_iff_le_mask mask_mono mask_shiftl_decompose order_trans shiftl_over_and_dist word_and_le' word_and_le2)

lemma mask_overlap_zero':
  "a \<ge> b \<Longrightarrow> (p AND NOT(mask a)) AND mask b = 0"
  for p :: \<open>'a::len word\<close>
  using mask_AND_NOT_mask mask_AND_less_0 by blast

lemma mask_rshift_mult_eq_rshift_lshift:
  "((a :: 'a :: len word) >> b) * (1 << c) = (a >> b << c)"
  by (simp add: shiftl_t2n)

lemma shift_alignment:
  "a \<ge> b \<Longrightarrow> is_aligned (p >> a << a) b"
  using is_aligned_shift is_aligned_weaken by blast

lemma mask_split_sum_twice:
  "a \<ge> b \<Longrightarrow> (p AND NOT(mask a)) + ((p AND mask a) AND NOT(mask b)) + (p AND mask b) = p"
  for p :: \<open>'a::len word\<close>
  by (simp add: add.commute multiple_mask_trivia word_bw_comms(1) word_bw_lcs(1) word_plus_and_or_coroll2)

lemma mask_shift_eq_mask_mask:
  "(p AND mask a >> b << b) = (p AND mask a) AND NOT(mask b)"
  for p :: \<open>'a::len word\<close>
  by (simp add: and_not_mask)

lemma mask_shift_sum:
  "\<lbrakk> a \<ge> b; unat n = unat (p AND mask b) \<rbrakk>
   \<Longrightarrow> (p AND NOT(mask a)) + (p AND mask a >> b) * (1 << b) + n = (p :: 'a :: len word)"
  by (metis and_not_mask mask_rshift_mult_eq_rshift_lshift mask_split_sum_twice word_eq_unatI)

lemma is_up_compose:
  "\<lbrakk> is_up uc; is_up uc' \<rbrakk> \<Longrightarrow> is_up (uc' \<circ> uc)"
  unfolding is_up_def by (simp add: Word.target_size Word.source_size)

lemma of_int_sint_scast:
  "of_int (sint (x :: 'a :: len word)) = (scast x :: 'b :: len word)"
  by (fact Word.of_int_sint)

lemma scast_of_nat_to_signed [simp]:
  "scast (of_nat x :: 'a :: len word) = (of_nat x :: 'a signed word)"
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma scast_of_nat_signed_to_unsigned_add:
  "scast (of_nat x + of_nat y :: 'a :: len signed word) = (of_nat x + of_nat y :: 'a :: len word)"
  by (metis of_nat_add scast_of_nat)

lemma scast_of_nat_unsigned_to_signed_add:
  "(scast (of_nat x + of_nat y :: 'a :: len word)) = (of_nat x + of_nat y :: 'a :: len signed word)"
  by (metis Abs_fnat_hom_add scast_of_nat_to_signed)

lemma and_mask_cases:
  fixes x :: "'a :: len word"
  assumes len: "n < LENGTH('a)"
  shows "x AND mask n \<in> of_nat ` set [0 ..< 2 ^ n]"
  using and_mask_less' len unat_less_power by (fastforce simp add: image_iff Bex_def)

lemma sint_eq_uint_2pl:
  "\<lbrakk> (a :: 'a :: len word) < 2 ^ (LENGTH('a) - 1) \<rbrakk>
   \<Longrightarrow> sint a = uint a"
  by (simp add: not_msb_from_less sint_eq_uint word_2p_lem word_size)

lemma pow_sub_less:
  "\<lbrakk> a + b \<le> LENGTH('a); unat (x :: 'a :: len word) = 2 ^ a \<rbrakk>
   \<Longrightarrow> unat (x * 2 ^ b - 1) < 2 ^ (a + b)"
  by (metis eq_or_less_helperD le_eq_less_or_eq power_add unat_eq_of_nat unat_lt2p word_unat_power)

lemma sle_le_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk> \<Longrightarrow> a <=s b"
  by (simp add: not_msb_from_less word_sle_msb_le)

lemma sless_less_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a < b \<rbrakk> \<Longrightarrow> a <s b"
  using not_msb_from_less word_sless_msb_less by blast

lemma and_mask2:
  "w << n >> n = w AND mask (size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp: bit_simps word_size)

lemma aligned_sub_aligned_simple:
  "\<lbrakk> is_aligned a n; is_aligned b n \<rbrakk> \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: aligned_sub_aligned)

lemma minus_one_shift:
  "- (1 << n) = (-1 << n :: 'a::len word)"
  by (simp add: shiftl_def minus_exp_eq_not_mask)

lemma ucast_eq_mask:
  "(UCAST('a::len \<rightarrow> 'b::len) x = UCAST('a \<rightarrow> 'b) y) =
   (x AND mask LENGTH('b) = y AND mask LENGTH('b))"
  by transfer (simp flip: take_bit_eq_mask add: ac_simps)

context
  fixes w :: "'a::len word"
begin

private lemma sbintrunc_uint_ucast:
  \<open>signed_take_bit n (uint (ucast w :: 'b word)) = signed_take_bit n (uint w)\<close> if \<open>Suc n = LENGTH('b::len)\<close>
  by (rule bit_eqI) (use that in \<open>auto simp: bit_simps\<close>)

private lemma test_bit_sbintrunc:
  assumes "i < LENGTH('a)"
  shows "bit (word_of_int (signed_take_bit n (uint w)) :: 'a word) i
           = (if n < i then bit w n else bit w i)"
  using assms by (simp add: bit_simps)

private lemma test_bit_sbintrunc_ucast:
  assumes len_a: "i < LENGTH('a)"
  shows "bit (word_of_int (signed_take_bit (LENGTH('b) - 1) (uint (ucast w :: 'b word))) :: 'a word) i
          = (if LENGTH('b::len) \<le> i then bit w (LENGTH('b) - 1) else bit w i)"
  using len_a by (auto simp: sbintrunc_uint_ucast bit_simps)

lemma scast_ucast_high_bits:
  \<open>scast (ucast w :: 'b::len word) = w
     \<longleftrightarrow> (\<forall> i \<in> {LENGTH('b) ..< size w}. bit w i = bit w (LENGTH('b) - 1))\<close>
proof (cases \<open>LENGTH('a) \<le> LENGTH('b)\<close>)
  case True
  moreover define m where \<open>m = LENGTH('b) - LENGTH('a)\<close>
  ultimately have \<open>LENGTH('b) = m + LENGTH('a)\<close>
    by simp
  then show ?thesis
    by (simp add: signed_ucast_eq word_size) word_eqI
next
  case False
  define q where \<open>q = LENGTH('b) - 1\<close>
  then have \<open>LENGTH('b) = Suc q\<close>
    by simp
  moreover define m where \<open>m = Suc LENGTH('a) - LENGTH('b)\<close>
  with False \<open>LENGTH('b) = Suc q\<close> have \<open>LENGTH('a) = m + q\<close>
    by (simp add: not_le)
  ultimately show ?thesis
    apply (simp add: signed_ucast_eq word_size)
    apply (transfer)
    apply (simp add: signed_take_bit_take_bit)
    apply (simp add: bit_eq_iff bit_take_bit_iff bit_signed_take_bit_iff min_def)
    by (metis atLeastLessThan_iff linorder_not_le nat_less_le not_less_eq)
qed

lemma scast_ucast_mask_compare:
  "scast (ucast w :: 'b::len word) = w
   \<longleftrightarrow> (w \<le> mask (LENGTH('b) - 1) \<or> NOT(mask (LENGTH('b) - 1)) \<le> w)"
  apply (clarsimp simp: le_mask_high_bits neg_mask_le_high_bits scast_ucast_high_bits word_size)
  apply (rule iffI; clarsimp)
   apply (rename_tac i j; case_tac "i = LENGTH('b) - 1"; case_tac "j = LENGTH('b) - 1")
  by auto

lemma ucast_less_shiftl_helper':
  "\<lbrakk> LENGTH('b) + (a::nat) < LENGTH('a); 2 ^ (LENGTH('b) + a) \<le> n\<rbrakk>
   \<Longrightarrow> (ucast (x :: 'b::len word) << a) < (n :: 'a::len word)"
  by (meson add_lessD1 order_less_le_trans shiftl_less_t2n' ucast_less)

end

lemma ucast_ucast_mask2:
  "is_down (UCAST ('a \<rightarrow> 'b)) \<Longrightarrow>
   UCAST ('b::len \<rightarrow> 'c::len) (UCAST ('a::len \<rightarrow> 'b::len) x) = UCAST ('a \<rightarrow> 'c) (x AND mask LENGTH('b))"
  by word_eqI_solve

lemma ucast_NOT:
  "ucast (NOT x) = NOT(ucast x) AND mask (LENGTH('a))" for x::"'a::len word"
  by word_eqI_solve

lemma ucast_NOT_down:
  "is_down UCAST('a::len \<rightarrow> 'b::len) \<Longrightarrow> UCAST('a \<rightarrow> 'b) (NOT x) = NOT(UCAST('a \<rightarrow> 'b) x)"
  by word_eqI

lemma upto_enum_step_shift:
  assumes "is_aligned p n"
  shows "([p , p + 2 ^ m .e. p + 2 ^ n - 1]) = map ((+) p) [0, 2 ^ m .e. 2 ^ n - 1]"
proof -
  consider "n < LENGTH('a)" | "p = 0" "n \<ge> LENGTH('a)"
    by (meson assms is_aligned_get_word_bits)
  then show ?thesis
  proof cases
    case 1
    with assms show ?thesis
      using is_aligned_no_overflow linorder_not_le
      by (force simp: upto_enum_step_def)
  qed (auto simp: map_idI)
qed


lemma upto_enum_step_shift_red:
  "\<lbrakk> is_aligned p sz; sz < LENGTH('a); us \<le> sz \<rbrakk>
     \<Longrightarrow> [p :: 'a :: len word, p + 2 ^ us .e. p + 2 ^ sz - 1]
          = map (\<lambda>x. p + of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]"
  by (simp add: upto_enum_step_red upto_enum_step_shift)

lemma upto_enum_step_subset:
  "set [x, y .e. z] \<subseteq> {x .. z}"
proof -
  have "\<And>w. \<lbrakk>x \<le> z; w \<le> (z - x) div (y - x)\<rbrakk>
          \<Longrightarrow> x \<le> x + w * (y - x) \<and> x + w * (y - x) \<le> z"
    by (metis add.commute div_to_mult_word_lt eq_diff_eq le_plus' word_plus_mono_right2)
  then show ?thesis
    by (auto simp: upto_enum_step_def linorder_not_less)
qed

lemma ucast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (ucast :: 'a word \<Rightarrow> 'b word)"
  shows "ucast (M a b) = M' (ucast a) (ucast b)"
  unfolding ucast_eq lift_M
  by (metis lift_M' local.distrib is_down ucast_down_wi uint_word_of_int word_of_int_uint)

lemma ucast_down_add:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) + b) = (ucast a + ucast b :: 'b::len word)"
  by (metis (mono_tags, opaque_lifting) of_int_add ucast_down_wi word_of_int_Ex)

lemma ucast_down_minus:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) - b) = (ucast a - ucast b :: 'b::len word)"
  by (metis add_diff_cancel_right' diff_add_cancel ucast_down_add)

lemma ucast_down_mult:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) * b) = (ucast a * ucast b :: 'b::len word)"
  by (simp add: mod_mult_eq take_bit_eq_mod ucast_distrib uint_word_arith_bintrs(3))

lemma scast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (scast :: 'a word \<Rightarrow> 'b word)"
  shows "scast (M a b) = M' (scast a) (scast b)"
proof -
  have \<section>: "is_down UCAST('a \<rightarrow> 'b)"
    using is_up_down is_down by blast
  then have "UCAST('a \<rightarrow> 'b) (M a b) = M' (UCAST('a \<rightarrow> 'b) a) (UCAST('a \<rightarrow> 'b) b)"
    using lift_M lift_M' local.distrib ucast_distrib by blast
  with \<section> show ?thesis
    using down_cast_same by fastforce
qed

lemma scast_down_add:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) + b) = (scast a + scast b :: 'b::len word)"
  by (metis down_cast_same is_up_down ucast_down_add)

lemma scast_down_minus:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) - b) = (scast a - scast b :: 'b::len word)"
  by (metis down_cast_same is_up_down ucast_down_minus)

lemma scast_down_mult:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) * b) = (scast a * scast b :: 'b::len word)"
  by (metis down_cast_same is_up_down ucast_down_mult)

lemma scast_ucast_1:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_ucast_3:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_ucast_4:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma scast_scast_b:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq sint_up_scast)

lemma ucast_scast_1:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq ucast_down_wi)

lemma ucast_scast_3:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_eq ucast_down_wi)

lemma ucast_scast_4:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis down_cast_same scast_eq sint_up_scast)

lemma ucast_ucast_a:
  "\<lbrakk> is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_eq ucast_down_wi)

lemma ucast_ucast_b:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis ucast_up_ucast)

lemma scast_scast_a:
  "\<lbrakk> is_down (scast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis down_cast_same is_down scast_eq ucast_down_wi)

lemma scast_down_wi [OF refl]:
  "uc = scast \<Longrightarrow> is_down uc \<Longrightarrow> uc (word_of_int x) = word_of_int x"
  by (metis down_cast_same is_up_down ucast_down_wi)

lemmas cast_simps =
  is_down is_up
  scast_down_add scast_down_minus scast_down_mult
  ucast_down_add ucast_down_minus ucast_down_mult
  scast_ucast_1 scast_ucast_3 scast_ucast_4
  ucast_scast_1 ucast_scast_3 ucast_scast_4
  ucast_ucast_a ucast_ucast_b
  scast_scast_a scast_scast_b
  ucast_down_wi scast_down_wi
  ucast_of_nat scast_of_nat
  uint_up_ucast sint_up_scast
  up_scast_surj up_ucast_surj

lemma sdiv_word_max:
    "(sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word) < (2 ^ (size a - 1))) =
          ((a \<noteq> - (2 ^ (size a - 1)) \<or> (b \<noteq> -1)))"
    (is "?lhs = (\<not> ?a_int_min \<or> \<not> ?b_minus1)")
proof (rule classical)
  assume not_thesis: "\<not> ?thesis"

  have not_zero: "b \<noteq> 0"
    using not_thesis by force

  let ?range = \<open>{- (2 ^ (size a - 1))..<2 ^ (size a - 1)} :: int set\<close>

  have result_range: "sint a sdiv sint b \<in> ?range \<union> {2 ^ (size a - 1)}"
    using sdiv_word_min [of a b] sdiv_word_max [of a b] by auto

  have result_range_overflow: "(sint a sdiv sint b = 2 ^ (size a - 1)) = (?a_int_min \<and> ?b_minus1)"
  proof -
    have False
      if "sint a sdiv sint b = 2 ^ (size a - 1)" "\<not> (a = - (2 ^ (size a - 1)) \<and> b = - 1)"
    proof (cases "?a_int_min")
      case True
      with that show ?thesis
        by (smt (verit, best) One_nat_def int_sdiv_negated_is_minus1 sint_int_min sint_minus1
            wsst_TYs(3) zero_less_power)
    next
      case False
      with that have "\<bar>sint a\<bar> < 2 ^ (size a - 1)"
        by (smt (verit, best) One_nat_def signed_word_eqI sint_ge sint_int_min sint_less wsst_TYs(3))
      then show ?thesis
        by (metis atLeastAtMost_iff not_less sdiv_int_range that(1))
    qed
    then  show ?thesis
      by (smt (verit, ccfv_SIG) One_nat_def int_sdiv_simps(3) sint_int_min sint_n1 wsst_TYs(3))
  qed
  then show ?thesis
    using result_range by auto
qed

lemmas sdiv_word_min' = sdiv_word_min [simplified word_size, simplified]
lemmas sdiv_word_max' = sdiv_word_max [simplified word_size, simplified]

lemma signed_arith_ineq_checks_to_eq:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a + sint b = sint (a + b ))"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a - sint b = sint (a - b))"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    = ((- sint a) = sint (- a))"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a * sint b = sint (a * b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a sdiv sint b = sint (a sdiv b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a smod sint b = sint (a smod b))"
  by (auto simp: sint_word_ariths word_size signed_div_arith signed_mod_arith signed_take_bit_int_eq_self_iff intro: sym dest: sym)

lemma signed_arith_sint:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a + b) = (sint a + sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a - b) = (sint a - sint b)"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    \<Longrightarrow> sint (- a) = (- sint a)"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a * b) = (sint a * sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a sdiv b) = (sint a sdiv sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a smod b) = (sint a smod sint b)"
  by (subst (asm) signed_arith_ineq_checks_to_eq; simp)+

lemma nasty_split_lt:
  \<open>x * 2 ^ n + (2 ^ n - 1) \<le> 2 ^ m - 1\<close>
    if \<open>x < 2 ^ (m - n)\<close> \<open>n \<le> m\<close> \<open>m < LENGTH('a::len)\<close>
    for x :: \<open>'a::len word\<close>
proof -
  define q where \<open>q = m - n\<close>
  with \<open>n \<le> m\<close> have \<open>m = q + n\<close>
    by simp
  with \<open>x < 2 ^ (m - n)\<close> have *: \<open>i < q\<close> if \<open>bit x i\<close> for i
    using that by simp (metis bit_take_bit_iff take_bit_word_eq_self_iff)
  from \<open>m = q + n\<close> have \<open>push_bit n x OR mask n \<le> mask m\<close>
    by (auto simp: le_mask_high_bits word_size bit_simps dest!: *)
  then have \<open>push_bit n x + mask n \<le> mask m\<close>
    by (simp add: disjunctive_add bit_simps)
  then show ?thesis
    by (simp add: mask_eq_exp_minus_1 push_bit_eq_mult)
qed

lemma is_aligned_shiftr_add:
 "\<lbrakk>is_aligned a n; is_aligned b m; b < 2^n; m \<le> n; n < LENGTH('a)\<rbrakk>
  \<Longrightarrow> a + b >> m = (a >> m) + (b >> m)" for a :: "'a::len word"
  apply(simp add: shiftr_div_2n_w word_size)
  apply (rule word_unat_eq_iff[THEN iffD2])
  apply (subst unat_plus_simple[THEN iffD1])
   apply (subst shiftr_div_2n_w[symmetric])+
   apply (rule is_aligned_no_wrap')
    apply (rule is_aligned_shiftr[where n = "n - m"])
    apply simp
   apply (rule shiftr_less_t2n)
   apply simp
  apply (simp add:unat_div)
  apply (subst unat_plus_simple[THEN iffD1])
   apply (erule is_aligned_no_wrap')
   apply simp
  by (meson div_plus_div_distrib_dvd_left is_aligned_iff_dvd_nat is_aligned_weaken)

lemma shiftr_eq_neg_mask_eq:
  "a >> b = c >> b \<Longrightarrow> a AND NOT (mask b) = c AND NOT (mask b)" for a :: "'a::len word"
  by word_eqI (metis less_eqE)

end

end
