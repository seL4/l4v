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
  using that
  apply (simp add: is_aligned_iff_udvd)
  apply transfer
  apply auto
  done

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
  apply (simp del: add_uminus_conv_diff add:diff_conv_add_uminus)
  apply (erule aligned_add_aligned, simp_all)
  apply (erule is_alignedE)
  apply (rule_tac k="- of_nat q" in is_alignedI)
  apply simp
  done

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
        apply (subst unat_of_nat)
        apply (rule mod_less)
        apply (rule order_less_trans [OF qv])
        apply (rule power_strict_increasing [OF diff_less [OF sne]])
         apply (simp_all)
        done

      have uptr: "unat ptr = 2 ^ sz * q"
        apply (subst ptrq)
        apply (subst iffD1 [OF unat_mult_lem])
         apply (subst unat_power_lower [OF szv])
         apply (subst uq)
         apply (rule nat_less_power_trans [OF qv order_less_imp_le [OF szv]])
        apply (subst uq)
        apply (subst unat_power_lower [OF szv])
        apply simp
        done

      show "unat ptr + unat off < 2 ^ LENGTH('a)" using szv
        apply (subst uptr)
        apply (subst mult.commute, rule nat_add_offset_less [OF _ qv])
        apply (rule order_less_le_trans [OF unat_mono [OF off] order_eq_refl])
         apply simp_all
        done
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
proof (induct xs arbitrary: n n')
  case Nil then show ?case by simp
next
  case (Cons y ys)
  from Cons.prems
  show ?case
    apply simp
    apply (cases "n = Suc (length ys)")
     apply (simp add: nth_append)
    apply (simp add: Suc_diff_le Cons.hyps nth_append)
    apply clarsimp
    apply arith
    done
qed

lemma drop_minus:
  "\<lbrakk> n < length xs; n' = length xs \<rbrakk> \<Longrightarrow> drop (n' - Suc n) xs = rev xs ! n  # drop (n' - n) xs"
  apply (subst drop_minus_lem)
     apply simp
    apply simp
   apply simp
  apply simp
  apply (cases "length xs", simp)
  apply (simp add: Suc_diff_le)
  done

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
  apply (erule aligned_add_aligned)
  apply (auto intro: is_alignedI [where k="x*z"])
  done

lemma is_aligned_add_multI:
  fixes p :: "'a::len word"
  shows "\<lbrakk>is_aligned p m; n \<le> m; n' = n\<rbrakk> \<Longrightarrow> is_aligned (p + x * 2 ^ n) n'"
  apply (erule aligned_add_aligned)
  apply (auto intro: is_alignedI [where k="x"])
  done

lemma is_aligned_no_wrap''':
  fixes ptr :: "'a::len word"
  shows"\<lbrakk> is_aligned ptr sz; sz < LENGTH('a); off < 2 ^ sz \<rbrakk>
         \<Longrightarrow> unat ptr + off < 2 ^ LENGTH('a)"
  apply (drule is_aligned_no_wrap[where off="of_nat off"])
   apply (simp add: word_less_nat_alt)
   apply (erule order_le_less_trans[rotated])
  apply (simp add: take_bit_eq_mod unsigned_of_nat)
  apply (subst(asm) unat_of_nat_len)
   apply (erule order_less_trans)
   apply (erule power_strict_increasing)
   apply simp
  apply assumption
  done

lemma is_aligned_get_word_bits:
  fixes p :: "'a::len word"
  shows "\<lbrakk> is_aligned p n; \<lbrakk> is_aligned p n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> P;
           \<lbrakk> p = 0; n \<ge> LENGTH('a) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases "n < LENGTH('a)")
   apply simp
  apply simp
  apply (erule meta_mp)
  apply (simp add: is_aligned_mask power_add power_overflow not_less
    flip: take_bit_eq_mask)
  apply (metis take_bit_length_eq take_bit_of_0 take_bit_tightened)
  done

lemma aligned_small_is_0:
  "\<lbrakk> is_aligned x n; x < 2 ^ n \<rbrakk> \<Longrightarrow> x = 0"
  by (simp add: is_aligned_mask less_mask_eq)

corollary is_aligned_less_sz:
  "\<lbrakk>is_aligned a sz; a \<noteq> 0\<rbrakk> \<Longrightarrow> \<not> a < 2 ^ sz"
  by (rule notI, drule(1) aligned_small_is_0, erule(1) notE)

lemma aligned_at_least_t2n_diff:
  "\<lbrakk>is_aligned x n; is_aligned y n; x < y\<rbrakk> \<Longrightarrow> x \<le> y - 2 ^ n"
  apply (erule is_aligned_get_word_bits[where p=y])
   apply (rule ccontr)
   apply (clarsimp simp: linorder_not_le)
   apply (subgoal_tac "y - x = 0")
    apply clarsimp
   apply (rule aligned_small_is_0)
    apply (erule(1) aligned_sub_aligned)
    apply simp
   apply unat_arith
  apply simp
  done

lemma is_aligned_no_overflow'':
  "\<lbrakk>is_aligned x n; x + 2 ^ n \<noteq> 0\<rbrakk> \<Longrightarrow> x \<le> x + 2 ^ n"
  apply (frule is_aligned_no_overflow')
  apply (erule order_trans)
  apply (simp add: field_simps)
  apply (erule word_sub_1_le)
  done

lemma is_aligned_bitI:
  \<open>is_aligned p m\<close> if \<open>\<And>n. n < m \<Longrightarrow> \<not> bit p n\<close>
  apply (simp add: is_aligned_mask)
  apply (rule bit_word_eqI)
  using that
  apply (auto simp add: bit_simps)
  done

lemma is_aligned_nth:
  "is_aligned p m = (\<forall>n < m. \<not> bit p n)"
  apply (auto intro: is_aligned_bitI simp add: is_aligned_mask bit_eq_iff)
   apply (auto simp: bit_simps)
  using bit_imp_le_length not_less apply blast
  done

lemma range_inter:
  "({a..b} \<inter> {c..d} = {}) = (\<forall>x. \<not>(a \<le> x \<and> x \<le> b \<and> c \<le> x \<and> x \<le> d))"
  by auto

lemma aligned_inter_non_empty:
  "\<lbrakk> {p..p + (2 ^ n - 1)} \<inter> {p..p + 2 ^ m - 1} = {};
     is_aligned p n; is_aligned p m\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp only: range_inter)
  apply (erule_tac x=p in allE)
  apply simp
  apply (erule impE)
   apply (erule is_aligned_no_overflow')
  apply (erule notE)
  apply (erule is_aligned_no_overflow)
  done

lemma not_aligned_mod_nz:
  assumes al: "\<not> is_aligned a n"
  shows "a mod 2 ^ n \<noteq> 0"
  apply (rule ccontr)
  using al apply (rule notE)
  apply simp
  apply (rule is_alignedI [of _ _ \<open>a div 2 ^ n\<close>])
  apply (metis add.right_neutral mult.commute word_mod_div_equality)
  done

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
        apply (subst unat_of_nat)
        apply (rule mod_less)
        apply (rule order_less_trans [OF qv])
        apply (rule power_strict_increasing [OF diff_less [OF sne]])
        apply simp_all
        done

      have uptr: "unat ptr = 2 ^ sz * q"
        apply (subst ptrq)
        apply (subst iffD1 [OF unat_mult_lem])
        apply (subst unat_power_lower [OF szv])
        apply (subst uq)
        apply (rule nat_less_power_trans [OF qv order_less_imp_le [OF szv]])
        apply (subst uq)
        apply (subst unat_power_lower [OF szv])
        apply simp
        done

      show "unat ptr + off \<le> 2 ^ LENGTH('a)" using szv
        apply (subst uptr)
        apply (subst mult.commute, rule nat_add_offset_le [OF off qv])
        apply simp
        done
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
  using that
  apply (cases \<open>n < LENGTH('a)\<close>)
  apply (simp_all add: not_less is_aligned_beyond_length)
  apply transfer
  apply (simp flip: take_bit_eq_0_iff)
  apply (subst take_bit_minus [symmetric])
  apply simp
  done

lemma add_mask_lower_bits:
  "\<lbrakk>is_aligned (x :: 'a :: len word) n;
    \<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> bit p n'\<rbrakk> \<Longrightarrow> x + p AND NOT (mask n) = x"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size is_aligned_nth)
   apply (erule_tac x=na in allE)+
   apply (simp add: bit_simps)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps not_less word_size)
  apply (metis is_aligned_nth not_le)
  done

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
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps is_aligned_nth)
  done

lemma is_aligned_shiftr_shiftl:
  "is_aligned w n \<Longrightarrow> w >> n << n = w"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps is_aligned_nth intro: ccontr)
  apply (subst add_diff_inverse_nat)
   apply (auto intro: ccontr)
  done

lemma aligned_shiftr_mask_shiftl:
  "is_aligned x n \<Longrightarrow> ((x >> n) AND mask v) << n = x AND mask (v + n)"
  apply (rule word_eqI)
  apply (simp add: word_size bit_simps)
  apply (subgoal_tac "\<forall>m. bit x m \<longrightarrow> m \<ge> n")
   apply auto[1]
  apply (clarsimp simp: is_aligned_mask)
  apply (drule_tac x=m in word_eqD)
  apply (frule test_bit_size)
  apply (simp add: word_size bit_simps)
  done

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
    apply (subst xv)
    apply (subst unat_mult_power_lem[OF kl])
    apply (subst mult.commute, rule nat_add_offset_less)
      apply (rule less_le_trans[OF unat_mono[OF offv, simplified]])
      apply (erule eq_imp_le[OF unat_power_lower])
     apply (rule kl)
    apply simp
   done
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
    apply (simp flip: take_bit_eq_mod)
    apply (rule bit_word_eqI)
    apply (auto simp add: bit_simps)
    apply (metis assms(2) bit_or_iff is_aligned_mask is_aligned_nth leD less_mask_eq word_and_le1 word_bw_lcs(1) word_neq_0_conv word_plus_and_or_coroll)
     apply (meson assms(2) leI less_2p_is_upper_bits_unset)
    apply (metis assms(2) bit_disjunctive_add_iff bit_imp_le_length bit_push_bit_iff is_alignedE' less_2p_is_upper_bits_unset)
    done
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
      apply -
      apply simp
      apply (subst (asm) add.commute, subst (asm) add.commute, drule word_plus_mcs_4)
       apply (subst add.commute, subst no_plus_overflow_uint_size)
       apply transfer
      apply simp
      apply (auto simp add: le_less power_2_ge_iff szv)
      apply (metis le_less_trans mask_eq_decr_exp mask_lt_2pn order_less_imp_le szv)
      done

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
  apply (subst (asm) is_aligned_mask)
  apply (drule less_mask_eq)
  apply (rule context_conjI)
   apply (subst word_plus_and_or_coroll)
    apply (simp_all flip: take_bit_eq_mask)
   apply (metis take_bit_eq_mask word_bw_lcs(1) word_log_esimps(1))
  apply (metis add.commute add_left_imp_eq take_bit_eq_mask word_plus_and_or_coroll2)
  done

lemmas mask_inner_mask = mask_eqs(1)

lemma mask_add_aligned:
  "is_aligned p n \<Longrightarrow> (p + q) AND mask n = q AND mask n"
  apply (simp add: is_aligned_mask)
  apply (subst mask_inner_mask [symmetric])
  apply simp
  done

lemma mask_out_add_aligned:
  assumes al: "is_aligned p n"
  shows "p + (q AND NOT (mask n)) = (p + q) AND NOT (mask n)"
  using mask_add_aligned [OF al]
  by (simp add: mask_out_sub_mask)

lemma is_aligned_add_or:
  "\<lbrakk>is_aligned p n; d < 2 ^ n\<rbrakk> \<Longrightarrow> p + d = p OR d"
  apply (subst disjunctive_add, simp_all)
  apply (clarsimp simp: is_aligned_nth less_2p_is_upper_bits_unset)
  subgoal for m
    apply (cases \<open>m < n\<close>)
     apply (auto simp add: not_less dest: bit_imp_possible_bit)
    done
  done

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
    apply (rule word_plus_mono_right)
     apply (rule order_less_imp_le, rule and_mask_less_size)
     apply (simp add: word_size word_bits)
    apply (rule is_aligned_no_overflow'', simp add: is_aligned_neg_mask word_bits)
    apply (rule not_greatest_aligned, rule b; simp add: is_aligned_neg_mask)
    done
  also have "\<dots> \<le> x AND NOT(mask n)"
    using b
    apply (subst add.commute)
    apply (rule le_plus)
     apply (rule aligned_at_least_t2n_diff; simp add: is_aligned_neg_mask)
    apply (rule ccontr, simp add: linorder_not_le)
    apply (drule aligned_small_is_0[rotated]; simp add: is_aligned_neg_mask)
    done
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
  "\<lbrakk>is_aligned (p::'a::len word) n; d < 2^n; n \<le> m; p < 2^m\<rbrakk> \<Longrightarrow> p + d < 2^m"
  apply (case_tac "m < LENGTH('a)")
   apply (subst mask_eq_iff_w2p[symmetric])
    apply (simp add: word_size)
   apply (simp add: is_aligned_add_or word_ao_dist less_mask_eq)
   apply (subst less_mask_eq)
    apply (erule order_less_le_trans)
    apply (erule(1) two_power_increasing)
   apply simp
  apply (simp add: power_overflow)
  done

lemma aligned_offset_non_zero:
  "\<lbrakk> is_aligned x n; y < 2 ^ n; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  apply (cases "y = 0")
   apply simp
  apply (subst word_neq_0_conv)
  apply (subst gt0_iff_gem1)
  apply (erule is_aligned_get_word_bits)
   apply (subst field_simps[symmetric], subst plus_le_left_cancel_nowrap)
     apply (rule is_aligned_no_wrap')
      apply simp
     apply (rule word_leq_le_minus_one)
      apply simp
     apply assumption
    apply (erule (1) is_aligned_no_wrap')
   apply (simp add: gt0_iff_gem1 [symmetric] word_neq_0_conv)
  apply simp
  done

lemma is_aligned_over_length:
  "\<lbrakk> is_aligned p n; LENGTH('a) \<le> n \<rbrakk> \<Longrightarrow> (p::'a::len word) = 0"
  by (simp add: is_aligned_mask mask_over_length)

lemma is_aligned_no_overflow_mask:
  "is_aligned x n \<Longrightarrow> x \<le> x + mask n"
  by (simp add: mask_eq_decr_exp) (erule is_aligned_no_overflow')

lemma aligned_mask_step:
  "\<lbrakk> n' \<le> n; p' \<le> p + mask n; is_aligned p n; is_aligned p' n' \<rbrakk> \<Longrightarrow>
   (p'::'a::len word) + mask n' \<le> p + mask n"
  apply (cases "LENGTH('a) \<le> n")
   apply (frule (1) is_aligned_over_length)
   apply (drule mask_over_length)
   apply clarsimp
  apply (simp add: not_le)
  apply (simp add: word_le_nat_alt unat_plus_simple)
  apply (subst unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)+
  apply (subst (asm) unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)
  apply (clarsimp simp: dvd_def is_aligned_iff_dvd_nat)
  apply (rename_tac k k')
  apply (thin_tac "unat p = x" for p x)+
  apply (subst Suc_le_mono[symmetric])
  apply (simp only: Suc_2p_unat_mask)
  apply (drule le_imp_less_Suc, subst (asm) Suc_2p_unat_mask, assumption)
  apply (erule (1) power_2_mult_step_le)
  done

lemma is_aligned_mask_offset_unat:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off \<le> mask sz"
  shows  "unat x + unat off < 2 ^ LENGTH('a)"
proof cases
  assume szv: "sz < LENGTH('a)"
  from al obtain k where xv: "x = 2 ^ sz * (of_nat k)"
    and kl: "k < 2 ^ (LENGTH('a) - sz)"
    by (auto elim: is_alignedE)

  from offv szv have offv': "unat off < 2 ^ sz"
    by (simp add: mask_2pm1 unat_less_power)

  show ?thesis using szv
    using al is_aligned_no_wrap''' offv' by blast
next
  assume "\<not> sz < LENGTH('a)"
  with al have "x = 0"
    by (meson is_aligned_get_word_bits)
  thus ?thesis by simp
qed

lemma aligned_less_plus_1:
  "\<lbrakk> is_aligned x n; n > 0 \<rbrakk> \<Longrightarrow> x < x + 1"
  apply (rule plus_one_helper2)
   apply (rule order_refl)
  apply (clarsimp simp: field_simps)
  apply (drule arg_cong[where f="\<lambda>x. x - 1"])
  apply (clarsimp simp: is_aligned_mask)
  done

lemma aligned_add_offset_less:
  "\<lbrakk>is_aligned x n; is_aligned y n; x < y; z < 2 ^ n\<rbrakk> \<Longrightarrow> x + z < y"
  apply (cases "y = 0")
   apply simp
  apply (erule is_aligned_get_word_bits[where p=y], simp_all)
  apply (cases "z = 0", simp_all)
  apply (drule(2) aligned_at_least_t2n_diff[rotated -1])
  apply (drule plus_one_helper2)
   apply (rule less_is_non_zero_p1)
   apply (rule aligned_less_plus_1)
    apply (erule aligned_sub_aligned[OF _ _ order_refl],
           simp_all add: is_aligned_triv)[1]
   apply (cases n, simp_all)[1]
  apply (simp only: trans[OF diff_add_eq diff_diff_eq2[symmetric]])
  apply (drule word_less_add_right)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule aligned_small_is_0, erule order_less_trans)
    apply (clarsimp simp: power_overflow)
   apply simp
  apply (erule order_le_less_trans[rotated],
         rule word_plus_mono_right)
   apply (erule word_le_minus_one_leq)
  apply (simp add: is_aligned_no_wrap' is_aligned_no_overflow field_simps)
  done

lemma gap_between_aligned:
  "\<lbrakk>a < (b :: 'a ::len word); is_aligned a n; is_aligned b n; n < LENGTH('a) \<rbrakk>
  \<Longrightarrow> a + (2^n - 1) < b"
  by (simp add: aligned_add_offset_less)

lemma is_aligned_add_step_le:
  "\<lbrakk> is_aligned (a::'a::len word) n; is_aligned b n; a < b; b \<le> a + mask n \<rbrakk> \<Longrightarrow> False"
  apply (simp flip: not_le)
  apply (erule notE)
  apply (cases "LENGTH('a) \<le> n")
   apply (drule (1) is_aligned_over_length)+
   apply (drule mask_over_length)
   apply clarsimp
  apply (clarsimp simp: word_le_nat_alt not_less not_le)
  apply (subst (asm) unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)
  apply (subst (asm) unat_add_lem' [symmetric])
   apply (simp add: is_aligned_mask_offset_unat)
  apply (metis gap_between_aligned linorder_not_less mask_eq_decr_exp unat_arith_simps(2))
  done

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
  and     s10: "0 < s1" (* Probably can be folded into the proof \<dots> *)
shows  "\<exists>q. m - n = of_nat q * 2 ^ s1 \<and> q < 2 ^ (s2 - s1)"
proof -
  have rl: "\<And>m s. \<lbrakk> m < 2 ^ (LENGTH('a) - s); s < LENGTH('a) \<rbrakk> \<Longrightarrow> unat ((2::'a word) ^ s * of_nat m) = 2 ^ s * m"
  proof -
    fix m :: nat and  s
    assume m: "m < 2 ^ (LENGTH('a) - s)" and s: "s < LENGTH('a)"
    then have "unat ((of_nat m) :: 'a word) = m"
      apply (subst unat_of_nat)
      apply (subst mod_less)
       apply (erule order_less_le_trans)
       apply (rule power_increasing)
        apply simp_all
      done

    then show "?thesis m s" using s m
      apply (subst iffD1 [OF unat_mult_lem])
      apply (simp add: nat_less_power_trans)+
      done
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
    by (simp add: of_nat_diff)
  finally have mn: "m - n = of_nat (mq - 2 ^ sq * nq) * 2 ^ s1" by simp
  moreover
  from nm have "m - n \<le> 2 ^ s2 - 1"
    by - (rule word_diff_ls', (simp add: field_simps)+)
  then have "(2::'a word) ^ s1 * of_nat (mq - 2 ^ sq * nq) < 2 ^ s2" using mn s2wb by (simp add: field_simps)
  then have "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (s2 - s1)"
  proof (rule word_power_less_diff)
    have mm: "mq - 2 ^ sq * nq < 2 ^ (LENGTH('a) - s1)" using mq by simp
    moreover from s10 have "LENGTH('a) - s1 < LENGTH('a)"
      by (rule diff_less, simp)
    ultimately show "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (LENGTH('a) - s1)"
      using take_bit_nat_less_self_iff [of \<open>LENGTH('a)\<close> \<open>mq - 2 ^ sq * nq\<close>]
      apply (auto simp add: word_less_nat_alt not_le not_less unsigned_of_nat)
      apply (metis take_bit_nat_eq_self_iff)
      done
  qed
  then have "mq - 2 ^ sq * nq < 2 ^ (s2 - s1)" using mq s2wb
    apply (simp add: word_less_nat_alt take_bit_eq_mod unsigned_of_nat)
    apply (subst (asm) mod_less)
    apply auto
     apply (rule order_le_less_trans)
      apply (rule diff_le_self)
     apply (erule order_less_le_trans)
    apply simp
    done
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
                                 of "%x. is_aligned x n" for n]]

lemma is_aligned_add:
  "\<lbrakk>is_aligned p n; is_aligned q n\<rbrakk> \<Longrightarrow> is_aligned (p + q) n"
  by (simp add: is_aligned_mask mask_add_aligned)

lemma aligned_shift:
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> (x + y) >> n = y >> n"
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps is_aligned_nth)
   apply (metis less_2p_is_upper_bits_unset not_le)
  apply (metis le_add1 less_2p_is_upper_bits_unset test_bit_bin)
  done

lemma aligned_shift':
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> (y + x) >> n = y >> n"
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps is_aligned_nth)
   apply (metis less_2p_is_upper_bits_unset not_le)
  apply (metis bit_imp_le_length le_add1 less_2p_is_upper_bits_unset)
  done

lemma and_neg_mask_plus_mask_mono: "(p AND NOT (mask n)) + mask n \<ge> p"
  for p :: \<open>'a::len word\<close>
  apply (rule word_le_minus_cancel[where x = "p AND NOT (mask n)"])
   apply (clarsimp simp: subtract_mask)
   using word_and_le1[where a = "mask n" and y = p]
    apply (clarsimp simp: mask_eq_decr_exp word_le_less_eq)
  apply (rule is_aligned_no_overflow'[folded mask_2pm1])
  apply (clarsimp simp: is_aligned_neg_mask)
  done

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
  "\<lbrakk>is_aligned ptr m; m \<le> n; a < 2 ^ m\<rbrakk>
   \<Longrightarrow> ptr + a AND mask n = (ptr AND mask n) + a"
  apply (rule mask_eqI[where n = m])
   apply (simp add:mask_twice min_def)
    apply (simp add:is_aligned_add_helper)
    apply (subst is_aligned_add_helper[THEN conjunct1])
      apply (erule is_aligned_after_mask)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "(ptr + a AND mask n) AND NOT (mask m)
     = (ptr + a AND NOT (mask m) ) AND mask n")
   apply (simp add:is_aligned_add_helper)
   apply (subst is_aligned_add_helper[THEN conjunct2])
     apply (simp add:is_aligned_after_mask)
    apply simp
   apply simp
  apply (simp add:word_bw_comms word_bw_lcs)
  done

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
    apply -
    apply (rule word_power_nonzero)
    apply (erule order_le_less_trans  [OF _ kw])
    apply (rule mw)
    apply (rule less_is_non_zero_p1 [OF ak])
    done
  then have "(a * 2 ^ m) + off < ((a + 1) * 2 ^ m)" using kw mw
    apply -
    apply (simp add: distrib_right)
    apply (rule word_plus_strict_mono_right [OF off])
    apply (rule is_aligned_no_overflow'')
    apply (rule is_aligned_mult_triv2)
    apply assumption
    done
  also have "\<dots> \<le> k * 2 ^ m" using ak1 mw kw False
    apply -
    apply (erule word_mult_le_mono1)
    apply (simp add: p2_gt_0)
    apply (simp add: word_less_nat_alt)
    apply (meson nat_mult_power_less_eq zero_less_numeral)
    done
  finally show ?thesis .
qed

lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::'a::len word) n; i > 0; i < 2 ^ n; n < LENGTH('a)\<rbrakk> \<Longrightarrow>
   \<not> is_aligned (p + of_nat i) n"
  apply (erule is_aligned_add_not_aligned)
  apply transfer
  apply (auto simp add: is_aligned_iff_udvd)
  apply (metis (no_types, lifting) le_less_trans less_not_refl2 less_or_eq_imp_le of_nat_eq_0_iff take_bit_eq_0_iff take_bit_nat_eq_self_iff take_bit_of_nat unat_lt2p unat_power_lower)
  done

lemma le_or_mask:
  "w \<le> w' \<Longrightarrow> w OR mask x \<le> w' OR mask x"
  for w w' :: \<open>'a::len word\<close>
  by (metis neg_mask_add_mask add.commute le_word_or1 mask_2pm1 neg_mask_mono_le word_plus_mono_left)

end

end
