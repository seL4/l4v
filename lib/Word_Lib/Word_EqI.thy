(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Solving Word Equalities"

theory Word_EqI
  imports
    Word_Next
    "HOL-Eisbach.Eisbach_Tools"
begin

text \<open>
  Some word equalities can be solved by considering the problem bitwise for all
  @{prop "n < LENGTH('a::len)"}, which is different to running @{text word_bitwise}
  and expanding into an explicit list of bits.
\<close>

lemma word_or_zero:
  "(a || b = 0) = (a = 0 \<and> b = 0)"
  by (safe; rule word_eqI, drule_tac x=n in word_eqD, simp)

lemma test_bit_over:
  "n \<ge> size (x::'a::len0 word) \<Longrightarrow> (x !! n) = False"
  by (simp add: test_bit_bl word_size)

lemma neg_mask_test_bit:
  "(~~(mask n) :: 'a :: len word) !! m = (n \<le> m \<and> m < LENGTH('a))"
  by (metis not_le nth_mask test_bit_bin word_ops_nth_size word_size)

lemma word_2p_mult_inc:
  assumes x: "2 * 2 ^ n < (2::'a::len word) * 2 ^ m"
  assumes suc_n: "Suc n < LENGTH('a::len)"
  shows "2^n < (2::'a::len word)^m"
  by (smt suc_n le_less_trans lessI nat_less_le nat_mult_less_cancel_disj p2_gt_0
          power_Suc power_Suc unat_power_lower word_less_nat_alt x)

lemma word_power_increasing:
  assumes x: "2 ^ x < (2 ^ y::'a::len word)" "x < LENGTH('a::len)" "y < LENGTH('a::len)"
  shows "x < y" using x
  apply (induct x arbitrary: y)
   apply (case_tac y; simp)
  apply (case_tac y; clarsimp simp: word_2p_mult_inc)
  apply (subst (asm) power_Suc [symmetric])
  apply (subst (asm) p2_eq_0)
  apply simp
  done

lemma upper_bits_unset_is_l2p:
  "n < LENGTH('a) \<Longrightarrow>
   (\<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> p !! n') = (p < 2 ^ n)" for p :: "'a :: len word"
  apply (cases "Suc 0 < LENGTH('a)")
   prefer 2
   apply (subgoal_tac "LENGTH('a) = 1", auto simp: word_eq_iff)[1]
  apply (rule iffI)
   apply (subst mask_eq_iff_w2p [symmetric])
    apply (clarsimp simp: word_size)
   apply (rule word_eqI, rename_tac n')
   apply (case_tac "n' < n"; simp add: word_size)
  by (meson bang_is_le le_less_trans not_le word_power_increasing)

lemma less_2p_is_upper_bits_unset:
  "p < 2 ^ n \<longleftrightarrow> n < LENGTH('a) \<and> (\<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> p !! n')" for p :: "'a :: len word"
  by (meson le_less_trans le_mask_iff_lt_2n upper_bits_unset_is_l2p word_zero_le)

lemma word_le_minus_one_leq:
  "x < y \<Longrightarrow> x \<le> y - 1" for x :: "'a :: len word"
  by (simp add: plus_one_helper)

lemma word_less_sub_le[simp]:
  fixes x :: "'a :: len word"
  assumes nv: "n < LENGTH('a)"
  shows "(x \<le> 2 ^ n - 1) = (x < 2 ^ n)"
  using le_less_trans word_le_minus_one_leq nv power_2_ge_iff by blast

lemma not_greatest_aligned:
  "\<lbrakk> x < y; is_aligned x n; is_aligned y n \<rbrakk> \<Longrightarrow> x + 2 ^ n \<noteq> 0"
  by (metis NOT_mask add_diff_cancel_right' diff_0 is_aligned_neg_mask_eq not_le word_and_le1)

lemma neg_mask_mono_le:
  "x \<le> y \<Longrightarrow> x && ~~(mask n) \<le> y && ~~(mask n)" for x :: "'a :: len word"
proof (rule ccontr, simp add: linorder_not_le, cases "n < LENGTH('a)")
  case False
  then show "y && ~~(mask n) < x && ~~(mask n) \<Longrightarrow> False"
    by (simp add: mask_def linorder_not_less power_overflow)
next
  case True
  assume a: "x \<le> y" and b: "y && ~~(mask n) < x && ~~(mask n)"
  have word_bits: "n < LENGTH('a)" by fact
  have "y \<le> (y && ~~(mask n)) + (y && mask n)"
    by (simp add: word_plus_and_or_coroll2 add.commute)
  also have "\<dots> \<le> (y && ~~(mask n)) + 2 ^ n"
    apply (rule word_plus_mono_right)
     apply (rule order_less_imp_le, rule and_mask_less_size)
     apply (simp add: word_size word_bits)
    apply (rule is_aligned_no_overflow'', simp add: is_aligned_neg_mask word_bits)
    apply (rule not_greatest_aligned, rule b; simp add: is_aligned_neg_mask)
    done
  also have "\<dots> \<le> x && ~~(mask n)"
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
  "w && ~~(mask n) = ~~(mask n) \<longleftrightarrow> ~~(mask n) \<le> w"
  by (metis eq_iff neg_mask_mono_le word_and_le1 word_and_le2 word_bw_same(1))

lemma le_mask_high_bits:
  "w \<le> mask n \<longleftrightarrow> (\<forall>i \<in> {n ..< size w}. \<not> w !! i)"
  by (auto simp: word_size and_mask_eq_iff_le_mask[symmetric] word_eq_iff)

lemma neg_mask_le_high_bits:
  "~~(mask n) \<le> w \<longleftrightarrow> (\<forall>i \<in> {n ..< size w}. w !! i)"
  by (auto simp: word_size and_neg_mask_eq_iff_not_mask_le[symmetric] word_eq_iff neg_mask_test_bit)

lemma test_bit_conj_lt:
  "(x !! m \<and> m < LENGTH('a)) = x !! m" for x :: "'a :: len word"
  using test_bit_bin by blast

lemma neg_test_bit:
  "(~~ x) !! n = (\<not> x !! n \<and> n < LENGTH('a))" for x :: "'a::len word"
  by (cases "n < LENGTH('a)") (auto simp add: test_bit_over word_ops_nth_size word_size)

named_theorems word_eqI_simps

lemmas [word_eqI_simps] =
  word_ops_nth_size
  word_size
  word_or_zero
  neg_mask_test_bit
  nth_ucast
  is_aligned_nth
  nth_w2p nth_shiftl
  nth_shiftr
  less_2p_is_upper_bits_unset
  le_mask_high_bits
  neg_mask_le_high_bits
  bang_eq
  neg_test_bit
  is_up
  is_down

lemmas word_eqI_rule = word_eqI[rule_format]

lemma test_bit_lenD:
  "x !! n \<Longrightarrow> n < LENGTH('a) \<and> x !! n" for x :: "'a :: len word"
  by (fastforce dest: test_bit_size simp: word_size)

method word_eqI uses simp simp_del split split_del cong flip =
  ((* reduce conclusion to test_bit: *)
   rule word_eqI_rule,
   (* make sure we're in clarsimp normal form: *)
   (clarsimp simp: simp simp del: simp_del simp flip: flip split: split split del: split_del cong: cong)?,
   (* turn x < 2^n assumptions into mask equations: *)
   ((drule less_mask_eq)+)?,
   (* expand and distribute test_bit everywhere: *)
   (clarsimp simp: word_eqI_simps simp simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* add any additional word size constraints to new indices: *)
   ((drule test_bit_lenD)+)?,
   (* try to make progress (can't use +, would loop): *)
   (clarsimp simp: word_eqI_simps simp simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* helps sometimes, rarely: *)
   (simp add: simp test_bit_conj_lt del: simp_del flip: flip split: split split del: split_del cong: cong)?)

method word_eqI_solve uses simp simp_del split split_del cong flip =
  solves \<open>word_eqI simp: simp simp_del: simp_del split: split split_del: split_del
                   cong: cong simp flip: flip;
          (fastforce dest: test_bit_size simp: word_eqI_simps simp flip: flip
                     simp: simp simp del: simp_del split: split split del: split_del cong: cong)?\<close>

end
