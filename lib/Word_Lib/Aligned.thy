(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Word Alignment"

theory Aligned
  imports
    "HOL-Library.Word"
    More_Word
    Bit_Shifts_Infix_Syntax

begin

context
  includes bit_operations_syntax
begin

lift_definition is_aligned :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> bool\<close>
  is \<open>\<lambda>k n. 2 ^ n dvd take_bit LENGTH('a) k\<close>
  by simp

lemma is_aligned_iff_udvd:
  \<open>is_aligned w n \<longleftrightarrow> 2 ^ n udvd w\<close>
  by transfer (simp flip: take_bit_eq_0_iff add: min_def)

lemma is_aligned_iff_take_bit_eq_0:
  \<open>is_aligned w n \<longleftrightarrow> take_bit n w = 0\<close>
  by (simp add: is_aligned_iff_udvd take_bit_eq_0_iff exp_dvd_iff_exp_udvd)

lemma is_aligned_iff_dvd_int:
  \<open>is_aligned ptr n \<longleftrightarrow> 2 ^ n dvd uint ptr\<close>
  by transfer simp

lemma is_aligned_iff_dvd_nat:
  \<open>is_aligned ptr n \<longleftrightarrow> 2 ^ n dvd unat ptr\<close>
proof -
  have \<open>unat ptr = nat \<bar>uint ptr\<bar>\<close>
    by transfer simp
  then have \<open>2 ^ n dvd unat ptr \<longleftrightarrow> 2 ^ n dvd uint ptr\<close>
    by (simp only: dvd_nat_abs_iff) simp
  then show ?thesis
    by (simp add: is_aligned_iff_dvd_int)
qed

lemma is_aligned_0 [simp]:
  \<open>is_aligned 0 n\<close>
  by transfer simp

lemma is_aligned_at_0 [simp]:
  \<open>is_aligned w 0\<close>
  by transfer simp

lemma is_aligned_beyond_length:
  \<open>is_aligned w n \<longleftrightarrow> w = 0\<close> if \<open>LENGTH('a) \<le> n\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: is_aligned_iff_take_bit_eq_0 take_bit_word_beyond_length_eq)

lemma is_alignedI [intro?]:
  \<open>is_aligned x n\<close> if \<open>x = 2 ^ n * k\<close> for x :: \<open>'a::len word\<close>
proof (unfold is_aligned_iff_udvd)
  from that show \<open>2 ^ n udvd x\<close>
    using dvd_triv_left exp_dvd_iff_exp_udvd by blast
qed

lemma is_alignedE:
  fixes w :: \<open>'a::len word\<close>
  assumes \<open>is_aligned w n\<close>
  obtains q where \<open>w = 2 ^ n * word_of_nat q\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close>
proof (cases \<open>n < LENGTH('a)\<close>)
  case False
  with assms have \<open>w = 0\<close>
    by (simp add: is_aligned_beyond_length)
  with that [of 0] show thesis
    by simp
next
  case True
  moreover define m where \<open>m = LENGTH('a) - n\<close>
  ultimately have l: \<open>LENGTH('a) = n + m\<close> and \<open>m \<noteq> 0\<close>
    by simp_all
  from \<open>n < LENGTH('a)\<close> have *: \<open>unat (2 ^ n :: 'a word) = 2 ^ n\<close>
    by transfer simp
  from assms have \<open>2 ^ n udvd w\<close>
    by (simp add: is_aligned_iff_udvd)
  then obtain v :: \<open>'a word\<close>
    where \<open>unat w = unat (2 ^ n :: 'a word) * unat v\<close> ..
  moreover define q where \<open>q = unat v\<close>
  ultimately have unat_w: \<open>unat w = 2 ^ n * q\<close>
    by (simp add: *)
  then have \<open>word_of_nat (unat w) = (word_of_nat (2 ^ n * q) :: 'a word)\<close>
    by simp
  then have w: \<open>w = 2 ^ n * word_of_nat q\<close>
    by simp
  moreover have \<open>q < 2 ^ (LENGTH('a) - n)\<close>
  proof (rule ccontr)
    assume \<open>\<not> q < 2 ^ (LENGTH('a) - n)\<close>
    then have \<open>2 ^ (LENGTH('a) - n) \<le> q\<close>
      by simp
    then have \<open>2 ^ LENGTH('a) \<le> 2 ^ n * q\<close>
      by (simp add: l power_add)
    with unat_w [symmetric] show False
      by (metis le_antisym nat_less_le unsigned_less)
  qed
  ultimately show thesis
    using that by blast
qed

lemma is_alignedE' [elim?]:
  fixes w :: \<open>'a::len word\<close>
  assumes \<open>is_aligned w n\<close>
  obtains q where \<open>w = push_bit n (word_of_nat q)\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close>
proof -
  from assms
  obtain q where \<open>w = 2 ^ n * word_of_nat q\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close>
    by (rule is_alignedE)
  then have \<open>w = push_bit n (word_of_nat q)\<close>
    by (simp add: push_bit_eq_mult)
  with that show thesis
    using \<open>q < 2 ^ (LENGTH('a) - n)\<close> .
qed

lemma is_aligned_mask:
  \<open>is_aligned w n \<longleftrightarrow> w AND mask n = 0\<close>
  by (simp add: is_aligned_iff_take_bit_eq_0 take_bit_eq_mask)

lemma is_aligned_imp_not_bit:
  \<open>\<not> bit w m\<close> if \<open>is_aligned w n\<close> and \<open>m < n\<close>
  for w :: \<open>'a::len word\<close>
proof -
  from \<open>is_aligned w n\<close>
  obtain q where \<open>w = push_bit n (word_of_nat q)\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close> ..
  moreover have \<open>\<not> bit (push_bit n (word_of_nat q :: 'a word)) m\<close>
    using \<open>m < n\<close> by (simp add: bit_simps)
  ultimately show ?thesis
    by simp
qed

lemma is_aligned_weaken:
  "\<lbrakk> is_aligned w x; x \<ge> y \<rbrakk> \<Longrightarrow> is_aligned w y"
  unfolding is_aligned_iff_dvd_nat
  by (erule dvd_trans [rotated]) (simp add: le_imp_power_dvd)

lemma is_alignedE_pre:
  fixes w::"'a::len word"
  assumes aligned: "is_aligned w n"
  shows        rl: "\<exists>q. w = 2 ^ n * (of_nat q) \<and> q < 2 ^ (LENGTH('a) - n)"
  using aligned is_alignedE by blast

lemma aligned_add_aligned:
  fixes x::"'a::len word"
  assumes aligned1: "is_aligned x n"
  and     aligned2: "is_aligned y m"
  and           lt: "m \<le> n"
  shows   "is_aligned (x + y) m"
proof cases
  assume nlt: "n < LENGTH('a)"
  show ?thesis
    unfolding is_aligned_iff_dvd_nat dvd_def
  proof -
    from aligned2 obtain q2 where yv: "y = 2 ^ m * of_nat q2"
      and q2v: "q2 < 2 ^ (LENGTH('a) - m)"
      by (auto elim: is_alignedE)

    from lt obtain k where kv: "m + k = n" by (auto simp: le_iff_add)
    with aligned1 obtain q1 where xv: "x = 2 ^ (m + k) * of_nat q1"
      and q1v: "q1 < 2 ^ (LENGTH('a) - (m + k))"
      by (auto elim: is_alignedE)

    have l1: "2 ^ (m + k) * q1 < 2 ^ LENGTH('a)"
      by (rule nat_less_power_trans [OF q1v])
         (subst kv, rule order_less_imp_le [OF nlt])

    have l2: "2 ^ m * q2 < 2 ^ LENGTH('a)"
      by (rule nat_less_power_trans [OF q2v],
          rule order_less_imp_le [OF order_le_less_trans])
         fact+

    have "x = of_nat (2 ^ (m + k) *  q1)" using xv
      by simp

    moreover have "y = of_nat (2 ^ m * q2)" using yv
      by simp

    ultimately have upls: "unat x + unat y = 2 ^ m * (2 ^ k * q1 + q2)"
    proof -
      have f1: "unat x = 2 ^ (m + k) * q1"
        using q1v unat_mult_power_lem xv by blast
      have "unat y = 2 ^ m * q2"
        using q2v unat_mult_power_lem yv by blast
      then show ?thesis
        using f1 by (simp add: power_add semiring_normalization_rules(34))
    qed

    (* (2 ^ k * q1 + q2) *)
    show "\<exists>d. unat (x + y) = 2 ^ m * d"
    proof (cases "unat x + unat y < 2 ^ LENGTH('a)")
      case True

      have "unat (x + y) = unat x + unat y"
        by (subst unat_plus_if', rule if_P) fact

      also have "\<dots> = 2 ^ m * (2 ^ k * q1 + q2)" by (rule upls)
      finally show ?thesis ..
    next
      case False
      then have "unat (x + y) = (unat x + unat y) mod 2 ^ LENGTH('a)"
        by (subst unat_word_ariths(1)) simp

      also have "\<dots> = (2 ^ m * (2 ^ k * q1 + q2)) mod 2 ^ LENGTH('a)"
        by (subst upls, rule refl)

      also
      have "\<dots> = 2 ^ m * ((2 ^ k * q1 +  q2) mod 2 ^ (LENGTH('a) - m))"
      proof -
        have "m \<le> len_of (TYPE('a))"
          by (meson le_trans less_imp_le_nat lt nlt)
        then show ?thesis
          by (metis mult_mod_right ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
      qed

      finally show ?thesis ..
    qed
  qed
next
  assume "\<not> n < LENGTH('a)"
  with assms
  show ?thesis
    by (simp add: is_aligned_mask not_less take_bit_eq_mod power_overflow word_arith_nat_defs(7) flip: take_bit_eq_mask)
qed

corollary aligned_sub_aligned:
  "\<lbrakk>is_aligned (x::'a::len word) n; is_aligned y m; m \<le> n\<rbrakk>
   \<Longrightarrow> is_aligned (x - y) m"
  by (metis (no_types, lifting) diff_zero is_aligned_mask is_aligned_weaken mask_eqs(4))

lemma is_aligned_shift:
  fixes k::"'a::len word"
  shows "is_aligned (k << m) m"
proof cases
  assume mv: "m < LENGTH('a)"
  from mv obtain q where mq: "m + q = LENGTH('a)" and "0 < q"
    by (auto dest: less_imp_add_positive)

  have "(2::nat) ^ m dvd unat (push_bit m k)"
  proof
    have kv: "(unat k div 2 ^ q) * 2 ^ q + unat k mod 2 ^ q = unat k"
      by (rule div_mult_mod_eq)

    have "unat (push_bit m k) = unat (2 ^ m * k)"
      by (simp add: push_bit_eq_mult ac_simps)
    also have "\<dots> = (2 ^ m * unat k) mod (2 ^ LENGTH('a))" using mv
      by (simp add: unat_word_ariths(2))
    also have "\<dots> = 2 ^ m * (unat k mod 2 ^ q)"
      by (subst mq [symmetric], subst power_add, subst mod_mult2_eq) simp
    finally show "unat (push_bit m k) = 2 ^ m * (unat k mod 2 ^ q)" .
  qed
  then show ?thesis by (unfold is_aligned_iff_dvd_nat shiftl_def)
next
  assume "\<not> m < LENGTH('a)"
  then show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask word_size shiftl_def)
qed

lemma aligned_mod_eq_0:
  fixes p::"'a::len word"
  assumes al: "is_aligned p sz"
  shows   "p mod 2 ^ sz = 0"
proof cases
  assume szv: "sz < LENGTH('a)"
  with al
  show ?thesis
    unfolding is_aligned_iff_dvd_nat
    by (simp add: and_mask_dvd_nat p2_gt_0 word_mod_2p_is_mask)
next
  assume "\<not> sz < LENGTH('a)"
  with al show ?thesis
    by (simp add: is_aligned_mask flip: take_bit_eq_mask take_bit_eq_mod)
qed

lemma is_aligned_triv: "is_aligned (2 ^ n ::'a::len word) n"
  by (rule is_alignedI [where k = 1], simp)

lemma is_aligned_mult_triv1: "is_aligned (2 ^ n * x  ::'a::len word) n"
  by (rule is_alignedI [OF refl])

lemma is_aligned_mult_triv2: "is_aligned (x * 2 ^ n ::'a::len word) n"
  by (subst mult.commute, simp add: is_aligned_mult_triv1)

lemma word_power_less_0_is_0:
  fixes x :: "'a::len word"
  shows "x < a ^ 0 \<Longrightarrow> x = 0" by simp

lemma is_aligned_no_wrap:
  fixes off :: "'a::len word"
  fixes ptr :: "'a::len word"
  assumes al: "is_aligned ptr sz"
  and    off: "off < 2 ^ sz"
  shows  "unat ptr + unat off < 2 ^ LENGTH('a)"
proof -
  have szv: "sz < LENGTH('a)"
  using off p2_gt_0 word_neq_0_conv by fastforce

  from al obtain q where ptrq: "ptr = 2 ^ sz * of_nat q" and
    qv: "q < 2 ^ (LENGTH('a) - sz)" by (auto elim: is_alignedE)

  show ?thesis
  proof (cases "sz = 0")
    case True
    then show ?thesis using off ptrq qv
      by simp
  next
    case False
    then have sne: "0 < sz" ..
    show ?thesis
    proof -
      have uq: "unat (of_nat q ::'a::len word) = q"
        by (metis diff_less le_unat_uoi len_gt_0 order_less_imp_le qv sne unat_power_lower)
      have uptr: "unat ptr = 2 ^ sz * q"
        by (simp add: ptrq qv unat_mult_power_lem)
      show "unat ptr + unat off < 2 ^ LENGTH('a)" using szv
        by (metis le_add_diff_inverse2 less_imp_le mult.commute nat_add_offset_less off qv unat_less_power uptr)
    qed
  qed
qed

lemma is_aligned_no_wrap':
  fixes ptr :: "'a::len word"
  assumes al: "is_aligned ptr sz"
  and    off: "off < 2 ^ sz"
  shows  "ptr \<le> ptr + off"
  by (subst no_plus_overflow_unat_size, subst word_size, rule is_aligned_no_wrap) fact+

lemma is_aligned_no_overflow':
  fixes p :: "'a::len word"
  assumes al: "is_aligned p n"
  shows "p \<le> p + (2 ^ n - 1)"
proof cases
  assume "n<LENGTH('a)"
  with al
  have "2^n - (1::'a::len word) < 2^n"
    by (simp add: word_less_nat_alt unat_sub_if_size)
  with al
  show ?thesis by (rule is_aligned_no_wrap')
next
  assume "\<not> n<LENGTH('a)"
  with al
  show ?thesis
  by (simp add: not_less power_overflow is_aligned_mask mask_2pm1)
qed

lemma is_aligned_no_overflow:
  "is_aligned ptr sz \<Longrightarrow> ptr \<le> ptr + 2^sz - 1"
  by (drule is_aligned_no_overflow') (simp add: field_simps)

lemma replicate_not_True:
  "\<And>n. xs = replicate n False \<Longrightarrow> True \<notin> set xs"
  by (induct xs) auto

lemma map_zip_replicate_False_xor:
  "n = length xs \<Longrightarrow> map (\<lambda>(x, y). x = (\<not> y)) (zip xs (replicate n False)) = xs"
  by (induct xs arbitrary: n, auto)

lemma drop_minus_lem:
  "\<lbrakk> n \<le> length xs; 0 < n; n' = length xs \<rbrakk> \<Longrightarrow> drop (n' - n) xs = rev xs ! (n - 1)  # drop (Suc (n' - n)) xs"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "n = Suc (length ys)")
    case True
    then show ?thesis
      using Cons.prems(3) rev_nth by fastforce
  next
    case False
    with Cons show ?thesis
      apply (simp add: rev_nth nth_append)
      by (simp add: Cons_nth_drop_Suc Suc_diff_le)
  qed
qed

lemma drop_minus:
  "\<lbrakk> n < length xs; n' = length xs \<rbrakk> \<Longrightarrow> drop (n' - Suc n) xs = rev xs ! n  # drop (n' - n) xs"
  by (simp add: Suc_diff_Suc drop_minus_lem)

lemma aligned_add_xor:
  \<open>(x + 2 ^ n) XOR 2 ^ n = x\<close>
  if al: \<open>is_aligned (x::'a::len word) n'\<close> and le: \<open>n < n'\<close>
proof -
  have \<open>\<not> bit x n\<close>
    using that by (rule is_aligned_imp_not_bit)
  then have \<open>x + 2 ^ n = x OR 2 ^ n\<close>
    by (subst disjunctive_add) (auto simp add: bit_simps disjunctive_add)
  moreover have \<open>(x OR 2 ^ n) XOR 2 ^ n = x\<close>
    by (rule bit_word_eqI) (auto simp add: bit_simps \<open>\<not> bit x n\<close>)
  ultimately show ?thesis
    by simp
qed

lemma is_aligned_add_mult_multI:
  fixes p :: "'a::len word"
  shows "\<lbrakk>is_aligned p m; n \<le> m; n' = n\<rbrakk> \<Longrightarrow> is_aligned (p + x * 2 ^ n * z) n'"
  by (metis aligned_add_aligned is_alignedI mult.assoc mult.commute)

lemma is_aligned_add_multI:
  fixes p :: "'a::len word"
  shows "\<lbrakk>is_aligned p m; n \<le> m; n' = n\<rbrakk> \<Longrightarrow> is_aligned (p + x * 2 ^ n) n'"
  by (simp add: aligned_add_aligned is_aligned_mult_triv2)

lemma is_aligned_no_wrap''':
  fixes ptr :: "'a::len word"
  shows "\<lbrakk> is_aligned ptr sz; sz < LENGTH('a); off < 2 ^ sz \<rbrakk>
         \<Longrightarrow> unat ptr + off < 2 ^ LENGTH('a)"
  by (metis is_alignedE le_add_diff_inverse2 less_imp_le mult.commute nat_add_offset_less unat_mult_power_lem)


(* this is not an actual elim rule, we need to preserve is_aligned, otherwise we lose information *)
lemma is_aligned_get_word_bits:
  fixes p :: "'a::len word"
  assumes "is_aligned p n"
  obtains "is_aligned p n" "n < LENGTH('a)" | "is_aligned p n" "p = 0" "n \<ge> LENGTH('a)"
  by (meson assms is_aligned_beyond_length linorder_not_le)

lemma aligned_small_is_0:
  "\<lbrakk> is_aligned x n; x < 2 ^ n \<rbrakk> \<Longrightarrow> x = 0"
  by (simp add: is_aligned_mask less_mask_eq)

corollary is_aligned_less_sz:
  "\<lbrakk>is_aligned a sz; a \<noteq> 0\<rbrakk> \<Longrightarrow> \<not> a < 2 ^ sz"
  by (rule notI, drule(1) aligned_small_is_0, erule(1) notE)

lemma aligned_at_least_t2n_diff:
  assumes x: "is_aligned x n"
      and y: "is_aligned y n"
      and "x < y"
    shows "x \<le> y - 2 ^ n"
  by (meson assms is_aligned_iff_udvd udvd_minus_le')

lemma is_aligned_no_overflow'':
  "\<lbrakk>is_aligned x n; x + 2 ^ n \<noteq> 0\<rbrakk> \<Longrightarrow> x \<le> x + 2 ^ n"
  using is_aligned_no_overflow order_trans word_sub_1_le by blast

lemma is_aligned_bitI:
  \<open>is_aligned p m\<close> if \<open>\<And>n. n < m \<Longrightarrow> \<not> bit p n\<close>
  by (simp add: bit_take_bit_iff bit_word_eqI is_aligned_iff_take_bit_eq_0 that)

lemma is_aligned_nth:
  "is_aligned p m = (\<forall>n < m. \<not> bit p n)"
  using is_aligned_bitI is_aligned_imp_not_bit by blast

lemma range_inter:
  "({a..b} \<inter> {c..d} = {}) = (\<forall>x. \<not>(a \<le> x \<and> x \<le> b \<and> c \<le> x \<and> x \<le> d))"
  by auto

lemma aligned_inter_non_empty:
  "\<lbrakk> {p..p + (2 ^ n - 1)} \<inter> {p..p + 2 ^ m - 1} = {};
     is_aligned p n; is_aligned p m\<rbrakk> \<Longrightarrow> False"
  by (simp add: is_aligned_no_overflow is_aligned_no_overflow')

lemma not_aligned_mod_nz:
  assumes al: "\<not> is_aligned a n"
  shows "a mod 2 ^ n \<noteq> 0"
  by (meson assms is_aligned_iff_udvd mod_eq_0_imp_udvd)

lemma nat_add_offset_le:
  fixes x :: nat
  assumes yv: "y \<le> 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y \<le> 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n"
    by (auto simp: le_iff_add)

  have "x * 2 ^ n + y \<le> x * 2 ^ n + 2 ^ n"
    using yv xv by simp
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y \<le> 2 ^ (m + n)" .
qed

lemma is_aligned_no_wrap_le:
  fixes ptr::"'a::len word"
  assumes al: "is_aligned ptr sz"
  and    szv: "sz < LENGTH('a)"
  and    off: "off \<le> 2 ^ sz"
  shows  "unat ptr + off \<le> 2 ^ LENGTH('a)"
proof -
  from al obtain q where ptrq: "ptr = 2 ^ sz * of_nat q" and
    qv: "q < 2 ^ (LENGTH('a) - sz)" by (auto elim: is_alignedE)

  show ?thesis
  proof (cases "sz = 0")
    case True
    then show ?thesis using off ptrq qv
      by (auto simp add: le_Suc_eq Suc_le_eq) (simp add: le_less)
  next
    case False
    then have sne: "0 < sz" ..

    show ?thesis
    proof -
      have uq: "unat (of_nat q :: 'a word) = q"
        by (metis diff_less le_unat_uoi len_gt_0 order_le_less qv sne unat_power_lower)
      have uptr: "unat ptr = 2 ^ sz * q"
        by (simp add: ptrq qv unat_mult_power_lem)
      show "unat ptr + off \<le> 2 ^ LENGTH('a)" using szv
        by (metis le_add_diff_inverse2 less_imp_le mult.commute nat_add_offset_le off qv uptr)
    qed
  qed
qed

lemma is_aligned_neg_mask:
  "m \<le> n \<Longrightarrow> is_aligned (x AND NOT (mask n)) m"
  by (rule is_aligned_bitI) (simp add: bit_simps)

lemma unat_minus:
  "unat (- (x :: 'a :: len word)) = (if x = 0 then 0 else 2 ^ size x - unat x)"
  using unat_sub_if_size[where x="2 ^ size x" and y=x]
  by (simp add: unat_eq_0 word_size)

lemma is_aligned_minus:
  \<open>is_aligned (- p) n\<close> if \<open>is_aligned p n\<close> for p :: \<open>'a::len word\<close>
  by (metis is_alignedE is_alignedI mult_minus_right that)

lemma add_mask_lower_bits:
  fixes x :: "'a :: len word"
  assumes "is_aligned x n"
    and "\<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> bit p n'"
  shows "x + p AND NOT (mask n) = x"
proof -
  have "x AND p = 0"
    by (metis assms bit_and_iff bit_imp_le_length is_aligned_nth not_le_imp_less word_exists_nth)
  moreover
  have "(x OR p) AND NOT (mask n) = x"
  proof (rule bit_word_eqI)
    fix k
    assume "k < LENGTH('a)"
    show "bit ((x OR p) AND NOT (mask n)) k = bit x k"
      by (metis assms is_aligned_mask mask_eq_0_eq_x neg_mask_test_bit word_ao_nth)
  qed
  ultimately show ?thesis
    by (simp add: word_plus_and_or_coroll)
qed

lemma is_aligned_andI1:
  "is_aligned x n \<Longrightarrow> is_aligned (x AND y) n"
  by (simp add: is_aligned_nth bit_simps)

lemma is_aligned_andI2:
  "is_aligned y n \<Longrightarrow> is_aligned (x AND y) n"
  by (simp add: is_aligned_nth bit_simps)

lemma is_aligned_shiftl:
  "is_aligned w (n - m) \<Longrightarrow> is_aligned (w << m) n"
  by (simp add: is_aligned_nth bit_simps)

lemma is_aligned_shiftr:
  "is_aligned w (n + m) \<Longrightarrow> is_aligned (w >> m) n"
  by (simp add: is_aligned_nth bit_simps)

lemma is_aligned_shiftl_self:
  "is_aligned (p << n) n"
  by (rule is_aligned_shift)

lemma is_aligned_neg_mask_eq:
  "is_aligned p n \<Longrightarrow> p AND NOT (mask n) = p"
  by (simp add: is_aligned_mask mask_eq_x_eq_0)

lemma is_aligned_shiftr_shiftl:
  "is_aligned w n \<Longrightarrow> w >> n << n = w"
  apply (rule bit_word_eqI)
  by (metis bit_shiftl_iff bit_shiftr_eq is_aligned_nth leI le_add_diff_inverse o_apply possible_bit_word)

lemma aligned_shiftr_mask_shiftl:
  assumes "is_aligned x n"
  shows "((x >> n) AND mask v) << n = x AND mask (v + n)"
proof -
  have "bit x m \<Longrightarrow> m \<ge> n" for m
    using assms is_aligned_imp_not_bit leI by blast
  with assms show ?thesis
    apply (intro word_eqI)
    by (metis bit_and_iff is_aligned_neg_mask_eq is_aligned_shiftr_shiftl push_bit_and push_bit_mask_eq shiftl_def)
qed

lemma mask_zero:
  "is_aligned x a \<Longrightarrow> x AND mask a = 0"
  by (metis is_aligned_mask)

lemma is_aligned_neg_mask_eq_concrete:
  "\<lbrakk> is_aligned p n; msk AND NOT (mask n) = NOT (mask n) \<rbrakk>
   \<Longrightarrow> p AND msk = p"
  by (metis word_bw_assocs(1) word_bw_comms(1) is_aligned_neg_mask_eq)

lemma is_aligned_and_not_zero:
  "\<lbrakk> is_aligned n k; n \<noteq> 0 \<rbrakk> \<Longrightarrow> 2 ^ k \<le> n"
  using is_aligned_less_sz leI by blast

lemma is_aligned_and_2_to_k:
  "(n AND 2 ^ k - 1) = 0 \<Longrightarrow> is_aligned (n :: 'a :: len word) k"
  by (simp add: is_aligned_mask mask_eq_decr_exp)

lemma is_aligned_power2:
  "b \<le> a \<Longrightarrow> is_aligned (2 ^ a) b"
  by (metis is_aligned_triv is_aligned_weaken)

lemma aligned_sub_aligned':
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; is_aligned b n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: aligned_sub_aligned)

lemma is_aligned_neg_mask_weaken:
  "\<lbrakk> is_aligned p n; m \<le> n \<rbrakk> \<Longrightarrow> p AND NOT (mask m) = p"
   using is_aligned_neg_mask_eq is_aligned_weaken by blast

lemma is_aligned_neg_mask2 [simp]:
  "is_aligned (a AND NOT (mask n)) n"
  by (rule is_aligned_bitI) (simp add: bit_simps)

lemma is_aligned_0':
  "is_aligned 0 n"
  by (fact is_aligned_0)

lemma aligned_add_offset_no_wrap:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off < 2 ^ sz"
  shows  "unat x + unat off < 2 ^ LENGTH('a)"
proof cases
  assume szv: "sz < LENGTH('a)"
  from al obtain k where xv: "x = 2 ^ sz * (of_nat k)"
    and kl: "k < 2 ^ (LENGTH('a) - sz)"
    by (auto elim: is_alignedE)

  show ?thesis using szv
    using al is_aligned_no_wrap offv by blast
next
  assume "\<not> sz < LENGTH('a)"
  with offv show ?thesis by (simp add: not_less power_overflow )
qed

lemma aligned_add_offset_mod:
  fixes x :: "('a::len) word"
  assumes al: "is_aligned x sz"
  and     kv: "k < 2 ^ sz"
  shows   "(x + k) mod 2 ^ sz = k"
proof cases
  assume szv: "sz < LENGTH('a)"

  have ux: "unat x + unat k < 2 ^ LENGTH('a)"
    by (rule aligned_add_offset_no_wrap) fact+

  show ?thesis using al szv
    by (metis add_0 assms(2) less_mask_eq mask_eqs(1) mask_zero word_gt_a_gt_0 word_mod_2p_is_mask)
next
  assume "\<not> sz < LENGTH('a)"
  with al show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask mask_eq_decr_exp
                  word_mod_by_0)
qed

lemma aligned_neq_into_no_overlap:
  fixes x :: "'a::len word"
  assumes neq: "x \<noteq> y"
  and     alx: "is_aligned x sz"
  and     aly: "is_aligned y sz"
  shows  "{x .. x + (2 ^ sz - 1)} \<inter> {y .. y + (2 ^ sz - 1)} = {}"
proof cases
  assume szv: "sz < LENGTH('a)"
  show ?thesis
  proof (rule equals0I, clarsimp)
    fix z
    assume xb: "x \<le> z" and xt: "z \<le> x + (2 ^ sz - 1)"
      and yb: "y \<le> z" and yt: "z \<le> y + (2 ^ sz - 1)"

    have rl: "\<And>(p::'a word) k w. \<lbrakk>uint p + uint k < 2 ^ LENGTH('a); w = p + k; w \<le> p + (2 ^ sz - 1) \<rbrakk>
      \<Longrightarrow> k < 2 ^ sz"
      by (smt (verit, best) no_olen_add szv uint_plus_simple_iff word_le_def word_less_sub_le)
    from xb obtain kx where
      kx: "z = x + kx" and
      kxl: "uint x + uint kx < 2 ^ LENGTH('a)"
      by (clarsimp dest!: word_le_exists')

    from yb obtain ky where
      ky: "z = y + ky" and
      kyl: "uint y + uint ky < 2 ^ LENGTH('a)"
      by (clarsimp dest!: word_le_exists')

    have "x = y"
    proof -
      have "kx = z mod 2 ^ sz"
      proof (subst kx, rule sym, rule aligned_add_offset_mod)
        show "kx < 2 ^ sz" by (rule rl) fact+
      qed fact+

      also have "\<dots> = ky"
      proof (subst ky, rule aligned_add_offset_mod)
        show "ky < 2 ^ sz"
          using kyl ky yt by (rule rl)
      qed fact+

      finally have kxky: "kx = ky" .
      moreover have "x + kx = y + ky" by (simp add: kx [symmetric] ky [symmetric])
      ultimately show ?thesis by simp
    qed
    then show False using neq by simp
  qed
next
  assume "\<not> sz < LENGTH('a)"
  with neq alx aly
  have False by (simp add: is_aligned_mask mask_eq_decr_exp power_overflow)
  then show ?thesis ..
qed

lemma is_aligned_add_helper:
  "\<lbrakk> is_aligned p n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p + d AND mask n = d) \<and> (p + d AND (NOT (mask n)) = p)"
  by (metis add_diff_cancel_left' add_mask_lower_bits less_2p_is_upper_bits_unset subtract_mask(2))

lemmas mask_inner_mask = mask_eqs(1)

lemma mask_add_aligned:
  "is_aligned p n \<Longrightarrow> (p + q) AND mask n = q AND mask n"
  by (metis add_0 mask_inner_mask mask_zero)

lemma mask_out_add_aligned:
  assumes al: "is_aligned p n"
  shows "p + (q AND NOT (mask n)) = (p + q) AND NOT (mask n)"
  using mask_add_aligned [OF al]
  by (simp add: mask_out_sub_mask)

lemma is_aligned_add_or:
  "\<lbrakk>is_aligned p n; d < 2 ^ n\<rbrakk> \<Longrightarrow> p + d = p OR d"
  by (metis and_zero_eq less_mask_eq mask_zero word_bw_assocs(1) word_bw_comms(1) word_plus_and_or_coroll)

lemma not_greatest_aligned:
  "\<lbrakk> x < y; is_aligned x n; is_aligned y n \<rbrakk> \<Longrightarrow> x + 2 ^ n \<noteq> 0"
  by (metis NOT_mask add_diff_cancel_right' diff_0 is_aligned_neg_mask_eq not_le word_and_le1)

lemma neg_mask_mono_le:
  "x \<le> y \<Longrightarrow> x AND NOT(mask n) \<le> y AND NOT(mask n)" for x :: "'a :: len word"
proof (rule ccontr, simp add: linorder_not_le, cases "n < LENGTH('a)")
  case False
  then show "y AND NOT(mask n) < x AND NOT(mask n) \<Longrightarrow> False"
    by (simp add: mask_eq_decr_exp linorder_not_less power_overflow)
next
  case True
  assume a: "x \<le> y" and b: "y AND NOT(mask n) < x AND NOT(mask n)"
  have word_bits: "n < LENGTH('a)" by fact
  have "y \<le> (y AND NOT(mask n)) + (y AND mask n)"
    by (simp add: word_plus_and_or_coroll2 add.commute)
  also have "\<dots> \<le> (y AND NOT(mask n)) + 2 ^ n"
  proof (rule word_plus_mono_right)
    show "y AND mask n \<le> 2 ^ n"
      by (metis and_mask_less' b linorder_not_le mask_exceed order_less_imp_le)
  next
    show "y AND NOT (mask n) \<le> (y AND NOT (mask n)) + 2 ^ n"
      using b is_aligned_neg_mask2 is_aligned_no_overflow'' not_greatest_aligned by blast
  qed
  also have "\<dots> \<le> x AND NOT(mask n)"
  proof -
    have "y AND NOT (mask n) \<le> (x AND NOT (mask n)) - 2 ^ n"
      by (simp add: aligned_at_least_t2n_diff b)
    moreover have "2 ^ n \<le> x AND NOT (mask n)"
      by (metis b is_aligned_mask is_aligned_neg_mask2 less_mask_eq linorder_not_le word_and_le2)
    ultimately show ?thesis
      by (metis add.commute le_plus)
  qed
  also have "\<dots> \<le> x" by (rule word_and_le2)
  also have "x \<le> y" by fact
  finally
  show "False" using b by simp
qed

lemma and_neg_mask_eq_iff_not_mask_le:
  "w AND NOT(mask n) = NOT(mask n) \<longleftrightarrow> NOT(mask n) \<le> w"
  for w :: \<open>'a::len word\<close>
  by (metis eq_iff neg_mask_mono_le word_and_le1 word_and_le2 word_bw_same(1))

lemma neg_mask_le_high_bits:
  \<open>NOT (mask n) \<le> w \<longleftrightarrow> (\<forall>i \<in> {n ..< size w}. bit w i)\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for w :: \<open>'a::len word\<close>
proof
  assume ?Q
  then have \<open>w AND NOT (mask n) = NOT (mask n)\<close>
    by (auto simp add: bit_simps word_size intro: bit_word_eqI)
  then show ?P
    by (simp add: and_neg_mask_eq_iff_not_mask_le)
next
  assume ?P
  then have *: \<open>w AND NOT (mask n) = NOT (mask n)\<close>
    by (simp add: and_neg_mask_eq_iff_not_mask_le)
  show \<open>?Q\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<forall>i\<in>{n..<size w}. bit w i)\<close>
    then obtain m where m: \<open>\<not> bit w m\<close> \<open>n \<le> m\<close> \<open>m < LENGTH('a)\<close>
      by (auto simp add: word_size)
    from * have \<open>bit (w AND NOT (mask n)) m \<longleftrightarrow> bit (NOT (mask n :: 'a word)) m\<close>
      by auto
    with m show False by (auto simp add: bit_simps)
  qed
qed

lemma is_aligned_add_less_t2n:
  fixes p :: "'a::len word"
  assumes "is_aligned p n"
      and "d < 2 ^ n"
      and "n \<le> m"
      and "p < 2 ^ m"
    shows "p + d < 2^m"
proof (cases "m < LENGTH('a)")
  case True
  have "m < size (p + d)"
    by (simp add: True word_size)
  moreover
  have "p + d AND mask m = p + d"
    using assms
    by (smt (verit, ccfv_SIG) is_aligned_add_helper less_mask_eq mask_eq_x_eq_0 mask_lower_twice)
  ultimately show ?thesis
    using True assms by (metis and_mask_less')
next
  case False
  then show ?thesis
    using \<open>p < 2 ^ m\<close> less_2p_is_upper_bits_unset by blast
qed

lemma aligned_offset_non_zero:
  "\<lbrakk> is_aligned x n; y < 2 ^ n; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  by (simp add: is_aligned_no_wrap' neq_0_no_wrap)

lemma is_aligned_over_length:
  "\<lbrakk> is_aligned p n; LENGTH('a) \<le> n \<rbrakk> \<Longrightarrow> (p::'a::len word) = 0"
  by (simp add: is_aligned_mask mask_over_length)

lemma is_aligned_no_overflow_mask:
  "is_aligned x n \<Longrightarrow> x \<le> x + mask n"
  by (simp add: mask_eq_decr_exp) (erule is_aligned_no_overflow')

lemma aligned_mask_step:
  fixes p' :: "'a::len word"
  assumes "n' \<le> n"
      and "p' \<le> p + mask n"
      and "is_aligned p n"
      and "is_aligned p' n'"
    shows "p' + mask n' \<le> p + mask n"
proof (cases "LENGTH('a) \<le> n")
  case True
  then show ?thesis
    using assms(3) is_aligned_over_length mask_over_length by fastforce
next
  case False
  obtain k k' where kk: "2 ^ n' * k' \<le> 2 ^ n * k + unat (mask n::'a word)"
    "unat p = 2 ^ n * k" "unat p' = 2 ^ n' * k'"
    using assms
    by (metis is_alignedE is_aligned_no_overflow_mask unat_mult_power_lem unat_plus_simple word_le_nat_alt)
  then have "2 ^ n' * (k' + 1) \<le> 2 ^ n * (k + 1)"
    by (metis False Suc_2p_unat_mask assms(1) leI le_imp_less_Suc power_2_mult_step_le)
  then have "2 ^ n' * k' + unat (mask n'::'a word) \<le> 2 ^ n * k + unat (mask n::'a word)"
    by (smt (verit, best) False Suc_2p_unat_mask assms(1) leI not_less_eq_eq order_le_less_trans)
  with assms kk show ?thesis
    by (metis is_aligned_no_overflow_mask unat_plus_simple word_le_nat_alt)
qed

lemma is_aligned_mask_offset_unat:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off \<le> mask sz"
  shows  "unat x + unat off < 2 ^ LENGTH('a)"
  using al is_aligned_no_overflow_mask no_olen_add_nat offv word_random by blast

lemma aligned_less_plus_1:
  assumes "is_aligned x n" and "0 < n"
  shows "x < x + 1"
proof (rule plus_one_helper2)
  show "x + 1 \<noteq> 0"
    using assms is_aligned_nth overflow_imp_lsb by blast
qed auto

lemma aligned_add_offset_less:
  assumes x: "is_aligned x n"
      and y: "is_aligned y n"
      and "x < y"
      and z: "z < 2 ^ n"
    shows "x + z < y"
proof (cases "y = 0 \<or> z = 0")
  case True
  then show ?thesis
    using \<open>x<y\<close> by auto
next
  case False
  with y is_aligned_get_word_bits have \<section>: "n < LENGTH('a)" "z \<noteq> 0"
    by auto
  then have "x \<le> y - 2 ^ n"
    by (simp add: aligned_at_least_t2n_diff assms(3) x y)
  with assms show ?thesis
    by (smt (verit, ccfv_SIG) False diff_add_cancel is_aligned_and_not_zero is_aligned_no_wrap'
                              not_less olen_add_eqv word_sub_mono2)
qed

lemma gap_between_aligned:
  "\<lbrakk>a < (b :: 'a ::len word); is_aligned a n; is_aligned b n; n < LENGTH('a) \<rbrakk>
  \<Longrightarrow> a + (2^n - 1) < b"
  by (simp add: aligned_add_offset_less)

lemma is_aligned_add_step_le:
  "\<lbrakk> is_aligned (a::'a::len word) n; is_aligned b n; a < b; b \<le> a + mask n \<rbrakk> \<Longrightarrow> False"
  by (metis gap_between_aligned is_aligned_get_word_bits leD linorder_neq_iff mask_eq_decr_exp)

lemma aligned_add_mask_lessD:
  "\<lbrakk> x + mask n < y; is_aligned x n \<rbrakk> \<Longrightarrow> x < y" for y::"'a::len word"
  by (metis is_aligned_no_overflow' mask_2pm1 order_le_less_trans)

lemma aligned_add_mask_less_eq:
  "\<lbrakk> is_aligned x n; is_aligned y n;  n < LENGTH('a) \<rbrakk> \<Longrightarrow> (x + mask n < y) = (x < y)"
  for y::"'a::len word"
  using aligned_add_mask_lessD is_aligned_add_step_le word_le_not_less by blast

lemma is_aligned_diff:
  fixes m :: "'a::len word"
  assumes alm: "is_aligned m s1"
  and     aln: "is_aligned n s2"
  and    s2wb: "s2 < LENGTH('a)"
  and      nm: "m \<in> {n .. n + (2 ^ s2 - 1)}"
  and    s1s2: "s1 \<le> s2"
shows  "\<exists>q. m - n = of_nat q * 2 ^ s1 \<and> q < 2 ^ (s2 - s1)"
proof (cases "s1=0")
  case True
  with nm have "unat(m-n) < 2 ^ s2"
    by simp (metis add.commute s2wb unat_less_power word_diff_ls'(4) word_less_sub_le)
  with True nm show ?thesis
    using unat_eq_of_nat by force
next
  case False
  have rl: "\<And>m s. \<lbrakk> m < 2 ^ (LENGTH('a) - s); s < LENGTH('a) \<rbrakk> \<Longrightarrow> unat ((2::'a word) ^ s * of_nat m) = 2 ^ s * m"
  proof -
    fix m :: nat and  s
    assume m: "m < 2 ^ (LENGTH('a) - s)" and s: "s < LENGTH('a)"
    then have "unat ((of_nat m) :: 'a word) = m"
      by (metis diff_le_self le_unat_uoi nat_less_le unat_of_nat_len unat_power_lower)
    then show "?thesis m s" using s m
      using unat_mult_power_lem by blast
  qed
  have s1wb: "s1 < LENGTH('a)" using s2wb s1s2 by simp
  from alm obtain mq where mmq: "m = 2 ^ s1 * of_nat mq" and mq: "mq < 2 ^ (LENGTH('a) - s1)"
    by (auto elim: is_alignedE simp: field_simps)
  from aln obtain nq where nnq: "n = 2 ^ s2 * of_nat nq" and nq: "nq < 2 ^ (LENGTH('a) - s2)"
    by (auto elim: is_alignedE simp: field_simps)
  from s1s2 obtain sq where sq: "s2 = s1 + sq" by (auto simp: le_iff_add)

  note us1 = rl [OF mq s1wb]
  note us2 = rl [OF nq s2wb]

  from nm have "n \<le> m" by clarsimp
  then have "(2::'a word) ^ s2 * of_nat nq \<le> 2 ^ s1 * of_nat mq" using nnq mmq by simp
  then have "2 ^ s2 * nq \<le> 2 ^ s1 * mq" using s1wb s2wb
    by (simp add: word_le_nat_alt us1 us2)
  then have nqmq: "2 ^ sq * nq \<le> mq" using sq by (simp add: power_add)

  have "m - n = 2 ^ s1 * of_nat mq - 2 ^ s2 * of_nat nq" using mmq nnq by simp
  also have "\<dots> = 2 ^ s1 * of_nat mq - 2 ^ s1 * 2 ^ sq * of_nat nq" using sq by (simp add: power_add)
  also have "\<dots> = 2 ^ s1 * (of_nat mq - 2 ^ sq * of_nat nq)" by (simp add: field_simps)
  also have "\<dots> = 2 ^ s1 * of_nat (mq - 2 ^ sq * nq)" using s1wb s2wb us1 us2 nqmq
    by simp
  finally have mn: "m - n = of_nat (mq - 2 ^ sq * nq) * 2 ^ s1" by simp
  moreover
  from nm have "m - n \<le> 2 ^ s2 - 1"
    by - (rule word_diff_ls', (simp add: field_simps)+)
  then have \<section>: "(2::'a word) ^ s1 * of_nat (mq - 2 ^ sq * nq) < 2 ^ s2"
    using mn s2wb by (simp add: field_simps)
  then have "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (s2 - s1)"
  proof (rule word_power_less_diff)
    have mm: "mq - 2 ^ sq * nq < 2 ^ (LENGTH('a) - s1)" using mq by simp
    moreover have "LENGTH('a) - s1 < LENGTH('a)"
      using False diff_less by blast
    ultimately show "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (LENGTH('a) - s1)"
      using of_nat_power by blast
  qed
  then have "mq - 2 ^ sq * nq < 2 ^ (s2 - s1)" using mq s2wb
    by (smt (verit, best) \<section> diff_le_self nat_power_less_diff order_le_less_trans unat_less_power
                          unat_mult_power_lem)
  ultimately show ?thesis
    by auto
qed

lemma is_aligned_addD1:
  assumes al1: "is_aligned (x + y) n"
  and     al2: "is_aligned (x::'a::len word) n"
  shows "is_aligned y n"
  using al2
proof (rule is_aligned_get_word_bits)
  assume "x = 0" then show ?thesis using al1 by simp
next
  assume nv: "n < LENGTH('a)"
  from al1 obtain q1
    where xy: "x + y = 2 ^ n * of_nat q1" and "q1 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  moreover from al2 obtain q2
    where x: "x = 2 ^ n * of_nat q2" and "q2 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  ultimately have "y = 2 ^ n * (of_nat q1 - of_nat q2)"
    by (simp add: field_simps)
  then show ?thesis using nv by (simp add: is_aligned_mult_triv1)
qed

lemmas is_aligned_addD2 =
       is_aligned_addD1[OF subst[OF add.commute,
                                 of "\<lambda>x. is_aligned x n" for n]]

lemma is_aligned_add:
  "\<lbrakk>is_aligned p n; is_aligned q n\<rbrakk> \<Longrightarrow> is_aligned (p + q) n"
  by (simp add: is_aligned_mask mask_add_aligned)

lemma aligned_shift:
  fixes x :: "'a::len word"
  assumes x: "x < 2 ^ n"
      and "is_aligned y n"
      and "n \<le> LENGTH('a::len)"
    shows "(x + y) >> n = y >> n"
proof (subst word_plus_and_or_coroll)
  show "x AND y = 0"
    using assms
    by (meson le_less_trans is_aligned_andI2 is_aligned_less_sz word_and_le2)
next
  show "x OR y >> n = y >> n"
    unfolding shiftr_def
    by (metis x drop_bit_or less_mask_eq or.left_neutral take_bit_eq_mask
              take_bit_eq_self_iff_drop_bit_eq_0)
qed

lemma aligned_shift':
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> (y + x) >> n = y >> n"
  by (simp add: add.commute aligned_shift)

lemma and_neg_mask_plus_mask_mono: "(p AND NOT (mask n)) + mask n \<ge> p"
  for p :: \<open>'a::len word\<close>
  by (metis le_word_or2 or_eq_and_not_plus)

lemma word_neg_and_le:
  "ptr \<le> (ptr AND NOT (mask n)) + (2 ^ n - 1)"
  for ptr :: \<open>'a::len word\<close>
  by (simp add: and_neg_mask_plus_mask_mono mask_2pm1[symmetric])

lemma is_aligned_sub_helper:
  "\<lbrakk> is_aligned (p - d) n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p AND mask n = d) \<and> (p AND (NOT (mask n)) = p - d)"
  by (drule(1) is_aligned_add_helper, simp)

lemma is_aligned_after_mask:
  "\<lbrakk>is_aligned k m;m\<le> n\<rbrakk> \<Longrightarrow> is_aligned (k AND mask n) m"
  by (rule is_aligned_andI1)

lemma and_mask_plus:
  assumes "is_aligned ptr m"
    and "m \<le> n"
    and "a < 2 ^ m"
  shows "ptr + a AND mask n = (ptr AND mask n) + a"
proof (rule mask_eqI)
  show "(ptr + a AND mask n) AND mask m = (ptr AND mask n) + a AND mask m"
    by (metis assms(2) mask_inner_mask mask_twice2)
next
  show "(ptr + a AND mask n) AND NOT (mask m) = (ptr AND mask n) + a AND NOT (mask m)"
    by (metis assms(1,3) is_aligned_add_helper is_aligned_neg_mask2 word_bw_assocs(1) word_bw_comms(1))
qed

lemma is_aligned_add_not_aligned:
  "\<lbrakk>is_aligned (p::'a::len word) n; \<not> is_aligned (q::'a::len word) n\<rbrakk> \<Longrightarrow> \<not> is_aligned (p + q) n"
  by (metis is_aligned_addD1)

lemma neg_mask_add_aligned:
  "\<lbrakk> is_aligned p n; q < 2 ^ n \<rbrakk> \<Longrightarrow> (p + q) AND NOT (mask n) = p AND NOT (mask n)"
  by (metis is_aligned_add_helper is_aligned_neg_mask_eq)

lemma word_add_power_off:
  fixes a :: "'a :: len word"
  assumes ak: "a < k"
  and kw: "k < 2 ^ (LENGTH('a) - m)"
  and mw: "m < LENGTH('a)"
  and off: "off < 2 ^ m"
shows "(a * 2 ^ m) + off < k * 2 ^ m"
proof (cases "m = 0")
  case True
  then show ?thesis using off ak by simp
next
  case False
  from ak have ak1: "a + 1 \<le> k" by (rule inc_le)
  then have "(a + 1) * 2 ^ m \<noteq> 0"
    by (meson ak kw less_is_non_zero_p1 mw order_le_less_trans word_power_nonzero)
  then have "(a * 2 ^ m) + off < ((a + 1) * 2 ^ m)" using kw mw
    by (simp add: distrib_right is_aligned_mult_triv2 is_aligned_no_overflow'' off
                  word_plus_strict_mono_right)
  also have "\<dots> \<le> k * 2 ^ m" using ak1 mw kw False
    by (simp add: less_2p_is_upper_bits_unset nat_mult_power_less_eq unat_less_power
                  word_mult_le_mono1)
  finally show ?thesis .
qed

lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::'a::len word) n; i > 0; i < 2 ^ n; n < LENGTH('a)\<rbrakk> \<Longrightarrow>
   \<not> is_aligned (p + of_nat i) n"
  by (metis of_nat_power Word.of_nat_neq_0 add.commute add.right_neutral is_aligned_addD1
            is_aligned_less_sz is_aligned_no_wrap''' unat_0)

lemma le_or_mask:
  "w \<le> w' \<Longrightarrow> w OR mask x \<le> w' OR mask x"
  for w w' :: \<open>'a::len word\<close>
  by (metis neg_mask_add_mask add.commute le_word_or1 mask_2pm1 neg_mask_mono_le word_plus_mono_left)

end

end
