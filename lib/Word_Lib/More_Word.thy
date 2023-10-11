(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Lemmas on words\<close>

theory More_Word
  imports
    "HOL-Library.Word"
    More_Arithmetic
    More_Divides
    More_Bit_Ring
begin

context
  includes bit_operations_syntax
begin

\<comment> \<open>problem posed by TPHOLs referee:
      criterion for overflow of addition of signed integers\<close>

lemma sofl_test:
  \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    drop_bit (size x - 1) ((x + y XOR x) AND (x + y XOR y)) = 0\<close>
  for x y :: \<open>'a::len word\<close>
proof -
  obtain n where n: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  have *: \<open>sint x + sint y + 2 ^ Suc n > signed_take_bit n (sint x + sint y) \<Longrightarrow> sint x + sint y \<ge> - (2 ^ n)\<close>
    \<open>signed_take_bit n (sint x + sint y) > sint x + sint y - 2 ^ Suc n \<Longrightarrow> 2 ^ n > sint x + sint y\<close>
    using signed_take_bit_int_greater_eq [of \<open>sint x + sint y\<close> n] signed_take_bit_int_less_eq [of n \<open>sint x + sint y\<close>]
    by (auto intro: ccontr)
  have \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (sint (x + y) < 0 \<longleftrightarrow> sint x < 0) \<or>
    (sint (x + y) < 0 \<longleftrightarrow> sint y < 0)\<close>
    using sint_less [of x] sint_greater_eq [of x] sint_less [of y] sint_greater_eq [of y]
    signed_take_bit_int_eq_self [of \<open>LENGTH('a) - 1\<close> \<open>sint x + sint y\<close>]
    apply (auto simp add: not_less)
       apply (unfold sint_word_ariths)
       apply (subst signed_take_bit_int_eq_self)
         prefer 4
         apply (subst signed_take_bit_int_eq_self)
           prefer 7
           apply (subst signed_take_bit_int_eq_self)
             prefer 10
             apply (subst signed_take_bit_int_eq_self)
               apply (auto simp add: signed_take_bit_int_eq_self signed_take_bit_eq_take_bit_minus take_bit_Suc_from_most n not_less intro!: *)
    done
  then show ?thesis
    apply (simp only: One_nat_def word_size drop_bit_eq_zero_iff_not_bit_last bit_and_iff bit_xor_iff)
    apply (simp add: bit_last_iff)
    done
qed

lemma unat_power_lower [simp]:
  "unat ((2::'a::len word) ^ n) = 2 ^ n" if "n < LENGTH('a::len)"
  using that by transfer simp

lemma unat_p2: "n < LENGTH('a :: len) \<Longrightarrow> unat (2 ^ n :: 'a word) = 2 ^ n"
  by (fact unat_power_lower)

lemma word_div_lt_eq_0:
  "x < y \<Longrightarrow> x div y = 0" for x :: "'a :: len word"
  by (fact div_word_less)

lemma word_div_eq_1_iff: "n div m = 1 \<longleftrightarrow> n \<ge> m \<and> unat n < 2 * unat (m :: 'a :: len word)"
  apply (simp only: word_arith_nat_defs word_le_nat_alt word_of_nat_eq_iff flip: nat_div_eq_Suc_0_iff)
  apply (simp flip: unat_div unsigned_take_bit_eq)
  done

lemma AND_twice [simp]:
  "(w AND m) AND m = w AND m"
  by (fact and.right_idem)

lemma word_combine_masks:
  "w AND m = z \<Longrightarrow> w AND m' = z' \<Longrightarrow> w AND (m OR m') = (z OR z')"
  for w m m' z z' :: \<open>'a::len word\<close>
  by (simp add: bit.conj_disj_distrib)

lemma p2_gt_0:
  "(0 < (2 ^ n :: 'a :: len word)) = (n < LENGTH('a))"
  by (simp add : word_gt_0 not_le)

lemma uint_2p_alt:
  \<open>n < LENGTH('a::len) \<Longrightarrow> uint ((2::'a::len word) ^ n) = 2 ^ n\<close>
  using p2_gt_0 [of n, where ?'a = 'a] by (simp add: uint_2p)

lemma p2_eq_0:
  \<open>(2::'a::len word) ^ n = 0 \<longleftrightarrow> LENGTH('a::len) \<le> n\<close>
  by (fact exp_eq_zero_iff)

lemma p2len:
  \<open>(2 :: 'a word) ^ LENGTH('a::len) = 0\<close>
  by (fact word_pow_0)

lemma neg_mask_is_div:
  "w AND NOT (mask n) = (w div 2^n) * 2^n"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI)
    (auto simp add: bit_simps simp flip: push_bit_eq_mult drop_bit_eq_div)

lemma neg_mask_is_div':
  "n < size w \<Longrightarrow> w AND NOT (mask n) = ((w div (2 ^ n)) * (2 ^ n))"
  for w :: \<open>'a::len word\<close>
  by (rule neg_mask_is_div)

lemma and_mask_arith:
  "w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI)
    (auto simp add: bit_simps word_size simp flip: push_bit_eq_mult drop_bit_eq_div)

lemma and_mask_arith':
  "0 < n \<Longrightarrow> w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  for w :: \<open>'a::len word\<close>
  by (rule and_mask_arith)

lemma mask_2pm1: "mask n = 2 ^ n - (1 :: 'a::len word)"
  by (fact mask_eq_decr_exp)

lemma add_mask_fold:
  "x + 2 ^ n - 1 = x + mask n"
  for x :: \<open>'a::len word\<close>
  by (simp add: mask_eq_decr_exp)

lemma word_and_mask_le_2pm1: "w AND mask n \<le> 2 ^ n - 1"
  for w :: \<open>'a::len word\<close>
  by (simp add: mask_2pm1[symmetric] word_and_le1)

lemma is_aligned_AND_less_0:
  "u AND mask n = 0 \<Longrightarrow> v < 2^n \<Longrightarrow> u AND v = 0"
  for u v :: \<open>'a::len word\<close>
  apply (drule less_mask_eq)
  apply (simp flip: take_bit_eq_mask)
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps)
  done

lemma and_mask_eq_iff_le_mask:
  \<open>w AND mask n = w \<longleftrightarrow> w \<le> mask n\<close>
  for w :: \<open>'a::len word\<close>
  apply (simp flip: take_bit_eq_mask)
  apply (cases \<open>n \<ge> LENGTH('a)\<close>; transfer)
   apply (simp_all add: not_le min_def)
   apply (simp_all add: mask_eq_exp_minus_1)
  apply auto
   apply (metis take_bit_int_less_exp)
  apply (metis min_def nat_less_le take_bit_int_eq_self_iff take_bit_take_bit)
  done

lemma less_eq_mask_iff_take_bit_eq_self:
  \<open>w \<le> mask n \<longleftrightarrow> take_bit n w = w\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: and_mask_eq_iff_le_mask take_bit_eq_mask)

lemma NOT_eq:
  "NOT (x :: 'a :: len word) = - x - 1"
  by (fact not_eq_complement)

lemma NOT_mask: "NOT (mask n :: 'a::len word) = - (2 ^ n)"
  by (simp add : NOT_eq mask_2pm1)

lemma le_m1_iff_lt: "(x > (0 :: 'a :: len word)) = ((y \<le> x - 1) = (y < x))"
  by uint_arith

lemma gt0_iff_gem1:
  \<open>0 < x \<longleftrightarrow> x - 1 < x\<close>
  for x :: \<open>'a::len word\<close>
  by (metis add.right_neutral diff_add_cancel less_irrefl measure_unat unat_arith_simps(2) word_neq_0_conv word_sub_less_iff)

lemma power_2_ge_iff:
  \<open>2 ^ n - (1 :: 'a::len word) < 2 ^ n \<longleftrightarrow> n < LENGTH('a)\<close>
  using gt0_iff_gem1 p2_gt_0 by blast

lemma le_mask_iff_lt_2n:
  "n < len_of TYPE ('a) = (((w :: 'a :: len word) \<le> mask n) = (w < 2 ^ n))"
  unfolding mask_2pm1 by (rule trans [OF p2_gt_0 [THEN sym] le_m1_iff_lt])

lemma mask_lt_2pn:
  \<open>n < LENGTH('a) \<Longrightarrow> mask n < (2 :: 'a::len word) ^ n\<close>
  by (simp add: mask_eq_exp_minus_1 power_2_ge_iff)

lemma word_unat_power:
  "(2 :: 'a :: len word) ^ n = of_nat (2 ^ n)"
  by simp

lemma of_nat_mono_maybe:
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  shows   "y < x \<Longrightarrow> of_nat y < (of_nat x :: 'a :: len word)"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (erule order_less_trans [OF _ xlt])
  apply (subst mod_less [OF xlt])
  apply assumption
  done

lemma word_and_max_word:
  fixes a::"'a::len word"
  shows "x = - 1 \<Longrightarrow> a AND x = a"
  by simp

lemma word_and_full_mask_simp:
  \<open>x AND mask LENGTH('a) = x\<close> for x :: \<open>'a::len word\<close>
  by (simp add: bit_eq_iff bit_simps)

lemma of_int_uint:
  "of_int (uint x) = x"
  by (fact word_of_int_uint)

corollary word_plus_and_or_coroll:
  "x AND y = 0 \<Longrightarrow> x + y = x OR y"
  for x y :: \<open>'a::len word\<close>
  by (fact disjunctive_add2)

corollary word_plus_and_or_coroll2:
  "(x AND w) + (x AND NOT w) = x"
  for x w :: \<open>'a::len word\<close>
  by (fact and_plus_not_and)

lemma unat_mask_eq:
  \<open>unat (mask n :: 'a::len word) = mask (min LENGTH('a) n)\<close>
  by transfer (simp add: nat_mask_eq)

lemma word_plus_mono_left:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y \<le> z; x \<le> x + z\<rbrakk> \<Longrightarrow> y + x \<le> z + x"
  by unat_arith

lemma less_Suc_unat_less_bound:
  "n < Suc (unat (x :: 'a :: len word)) \<Longrightarrow> n < 2 ^ LENGTH('a)"
  by (auto elim!: order_less_le_trans intro: Suc_leI)

lemma up_ucast_inj:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> len_of TYPE ('b) \<rbrakk> \<Longrightarrow> x = (y::'a::len word)"
  by transfer (simp add: min_def split: if_splits)

lemmas ucast_up_inj = up_ucast_inj

lemma up_ucast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow> (ucast x = (ucast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_ucast_inj)

lemma no_plus_overflow_neg:
  "(x :: 'a :: len word) < -y \<Longrightarrow> x \<le> x + y"
  by (metis diff_minus_eq_add less_imp_le sub_wrap_lt)

lemma ucast_ucast_eq:
  "\<lbrakk> ucast x = (ucast (ucast y::'a word)::'c::len word); LENGTH('a) \<le> LENGTH('b);
     LENGTH('b) \<le> LENGTH('c) \<rbrakk> \<Longrightarrow>
   x = ucast y" for x :: "'a::len word" and y :: "'b::len word"
  apply transfer
  apply (cases \<open>LENGTH('c) = LENGTH('a)\<close>)
   apply (auto simp add: min_def)
  done

lemma ucast_0_I:
  "x = 0 \<Longrightarrow> ucast x = 0"
  by simp

lemma word_add_offset_less:
  fixes x :: "'a :: len word"
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mnv: "sz < LENGTH('a :: len)"
  and    xv': "x < 2 ^ (LENGTH('a :: len) - n)"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from mnv mn have nv: "n < LENGTH('a)" and mv: "m < LENGTH('a)"  by auto

  have uy: "unat y < 2 ^ n"
    by (rule order_less_le_trans [OF unat_mono [OF yv] order_eq_refl],
        rule unat_power_lower[OF nv])

  have ux: "unat x < 2 ^ m"
    by (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl],
        rule unat_power_lower[OF mv])

  then show "x * 2 ^ n + y < 2 ^ (m + n)" using ux uy nv mnv xv'
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)+
    apply (subst mod_less)
     apply simp
     apply (subst mult.commute)
     apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
     apply (rule order_less_le_trans [OF unat_mono [OF xv']])
     apply (cases "n = 0"; simp)
    apply (subst unat_power_lower[OF nv])
    apply (subst mod_less)
     apply (erule order_less_le_trans [OF nat_add_offset_less], assumption)
      apply (rule mn)
     apply simp
    apply (simp add: mn mnv)
    apply (erule nat_add_offset_less; simp)
    done
qed

lemma word_less_power_trans:
  fixes n :: "'a :: len word"
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  and     mv: "m < len_of TYPE ('a)"
  shows "2 ^ k * n < 2 ^ m"
  using nv kv mv
  apply -
  apply (subst word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply simp
   apply (rule nat_less_power_trans)
    apply (erule order_less_trans [OF unat_mono])
    apply simp
   apply simp
  apply simp
  apply (rule nat_less_power_trans)
   apply (subst unat_power_lower[where 'a = 'a, symmetric])
    apply simp
   apply (erule unat_mono)
  apply simp
  done

lemma  word_less_power_trans2:
  fixes n :: "'a::len word"
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk> \<Longrightarrow> n * 2 ^ k < 2 ^ m"
  by (subst field_simps, rule word_less_power_trans)

lemma Suc_unat_diff_1:
  fixes x :: "'a :: len word"
  assumes lt: "1 \<le> x"
  shows "Suc (unat (x - 1)) = unat x"
proof -
  have "0 < unat x"
    by (rule order_less_le_trans [where y = 1], simp, subst unat_1 [symmetric],
        rule iffD1 [OF word_le_nat_alt lt])

  then show ?thesis
    by ((subst unat_sub [OF lt])+, simp only:  unat_1)
qed

lemma word_eq_unatI:
  \<open>v = w\<close> if \<open>unat v = unat w\<close>
  using that by transfer (simp add: nat_eq_iff)

lemma word_div_sub:
  fixes x :: "'a :: len word"
  assumes yx: "y \<le> x"
  and     y0: "0 < y"
  shows "(x - y) div y = x div y - 1"
  apply (rule word_eq_unatI)
  apply (subst unat_div)
  apply (subst unat_sub [OF yx])
  apply (subst unat_sub)
   apply (subst word_le_nat_alt)
   apply (subst unat_div)
   apply (subst le_div_geq)
     apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
     apply simp
    apply (subst word_le_nat_alt [symmetric], rule yx)
   apply simp
  apply (subst unat_div)
  apply (subst le_div_geq [OF _ iffD1 [OF word_le_nat_alt yx]])
   apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
   apply simp
  apply simp
  done

lemma word_mult_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k < j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto intro: order_less_subst2 simp: word_less_nat_alt elim: mult_less_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_less_dest:
  fixes i :: "'a :: len word"
  assumes ij: "i * k < j * k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk ij
  by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem] elim: mult_less_mono1)

lemma word_mult_less_cancel:
  fixes k :: "'a :: len word"
  assumes knz: "0 < k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows "(i * k < j * k) = (i < j)"
  by (rule iffI [OF word_mult_less_dest [OF _ uik ujk] word_mult_less_mono1 [OF _ knz ujk]])

lemma Suc_div_unat_helper:
  assumes szv: "sz < LENGTH('a :: len)"
  and   usszv: "us \<le> sz"
  shows "2 ^ (sz - us) = Suc (unat (((2::'a :: len word) ^ sz - 1) div 2 ^ us))"
proof -
  note usv = order_le_less_trans [OF usszv szv]

  from usszv obtain q where qv: "sz = us + q" by (auto simp: le_iff_add)

  have "Suc (unat (((2:: 'a word) ^ sz - 1) div 2 ^ us)) =
    (2 ^ us + unat ((2:: 'a word) ^ sz - 1)) div 2 ^ us"
    apply (subst unat_div unat_power_lower[OF usv])+
    apply (subst div_add_self1, simp+)
    done

  also have "\<dots> = ((2 ^ us - 1) + 2 ^ sz) div 2 ^ us" using szv
    by (simp add: unat_minus_one)

  also have "\<dots> = 2 ^ q + ((2 ^ us - 1) div 2 ^ us)"
    apply (subst qv)
    apply (subst power_add)
    apply (subst div_mult_self2; simp)
    done

  also have "\<dots> = 2 ^ (sz - us)" using qv by simp

  finally show ?thesis ..
qed

lemma enum_word_nth_eq:
  \<open>(Enum.enum :: 'a::len word list) ! n = word_of_nat n\<close>
    if \<open>n < 2 ^ LENGTH('a)\<close>
    for n
  using that by (simp add: enum_word_def)

lemma length_enum_word_eq:
  \<open>length (Enum.enum :: 'a::len word list) = 2 ^ LENGTH('a)\<close>
  by (simp add: enum_word_def)

lemma unat_lt2p [iff]:
  \<open>unat x < 2 ^ LENGTH('a)\<close> for x :: \<open>'a::len word\<close>
  by transfer simp

lemma of_nat_unat [simp]:
  "of_nat \<circ> unat = id"
  by (rule ext, simp)

lemma Suc_unat_minus_one [simp]:
  "x \<noteq> 0 \<Longrightarrow> Suc (unat (x - 1)) = unat x"
  by (metis Suc_diff_1 unat_gt_0 unat_minus_one)

lemma word_add_le_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k \<le> j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i \<le> j"
  using uik ujk le
  by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem] elim: add_le_mono1)

lemma word_add_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k \<le> j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: add_le_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_le_mono2:
  fixes i :: "'a :: len word"
  shows "\<lbrakk>i \<le> j; unat j + unat k < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> k + i \<le> k + j"
  by (subst field_simps, subst field_simps, erule (1) word_add_le_mono1)

lemma word_add_le_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k \<le> j + k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i + k \<le> j + k" by (rule word_add_le_mono1) fact+
next
  assume "i + k \<le> j + k"
  show "i \<le> j" by (rule word_add_le_dest) fact+
qed

lemma word_add_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k < j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_less_nat_alt elim: add_less_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_less_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k < j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk le
  by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem] elim: add_less_mono1)

lemma word_add_less_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k < j + k) = (i < j)"
proof
  assume "i < j"
  show "i + k < j + k" by (rule word_add_less_mono1) fact+
next
  assume "i + k < j + k"
  show "i < j" by (rule word_add_less_dest) fact+
qed

lemma word_mult_less_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k < j * k) = (i < j)"
  using assms by (rule word_mult_less_cancel)

lemma word_le_imp_diff_le:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> n - k \<le> m"
  by (auto simp: unat_sub word_le_nat_alt)

lemma word_less_imp_diff_less:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n < m\<rbrakk> \<Longrightarrow> n - k < m"
  by (clarsimp simp: unat_sub word_less_nat_alt
             intro!: less_imp_diff_less)

lemma word_mult_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k \<le> j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: mult_le_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_le_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k \<le> j * k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i * k \<le> j * k" by (rule word_mult_le_mono1) fact+
next
  assume p: "i * k \<le> j * k"

  have "0 < unat k" using knz by (simp add: word_less_nat_alt)
  then show "i \<le> j" using p
    by (clarsimp simp: word_le_nat_alt iffD1 [OF unat_mult_lem uik]
      iffD1 [OF unat_mult_lem ujk])
qed

lemma word_diff_less:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>0 < n; 0 < m; n \<le> m\<rbrakk> \<Longrightarrow> m - n < m"
  apply (subst word_less_nat_alt)
  apply (subst unat_sub)
   apply assumption
  apply (rule diff_less)
   apply (simp_all add: word_less_nat_alt)
  done

lemma word_add_increasing:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p + w \<le> x; p \<le> p + w \<rbrakk> \<Longrightarrow> p \<le> x"
  by unat_arith

lemma word_random:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p \<le> p + x'; x \<le> x' \<rbrakk> \<Longrightarrow> p \<le> p + x"
  by unat_arith

lemma word_sub_mono:
  "\<lbrakk> a \<le> c; d \<le> b; a - b \<le> a; c - d \<le> c \<rbrakk>
    \<Longrightarrow> (a - b) \<le> (c - d :: 'a :: len word)"
  by unat_arith

lemma power_not_zero:
  "n < LENGTH('a::len) \<Longrightarrow> (2 :: 'a word) ^ n \<noteq> 0"
  by (metis p2_gt_0 word_neq_0_conv)

lemma word_gt_a_gt_0:
  "a < n \<Longrightarrow> (0 :: 'a::len word) < n"
  apply (case_tac "n = 0")
   apply clarsimp
  apply (clarsimp simp: word_neq_0_conv)
  done

lemma word_power_less_1 [simp]:
  "sz < LENGTH('a::len) \<Longrightarrow> (2::'a word) ^ sz - 1 < 2 ^ sz"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_minus_one)
  apply simp_all
  done

lemma word_sub_1_le:
  "x \<noteq> 0 \<Longrightarrow> x - 1 \<le> (x :: 'a :: len word)"
  apply (subst no_ulen_sub)
  apply simp
  apply (cases "uint x = 0")
   apply (simp add: uint_0_iff)
  apply (insert uint_ge_0[where x=x])
  apply arith
  done

lemma push_bit_word_eq_nonzero:
  \<open>push_bit n w \<noteq> 0\<close> if \<open>w < 2 ^ m\<close> \<open>m + n < LENGTH('a)\<close> \<open>w \<noteq> 0\<close>
    for w :: \<open>'a::len word\<close>
  using that
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt)
  apply (metis add_diff_cancel_right' gr0I gr_implies_not0 less_or_eq_imp_le min_def push_bit_eq_0_iff take_bit_nat_eq_self_iff take_bit_push_bit take_bit_take_bit unsigned_push_bit_eq)
  done

lemma unat_less_power:
  fixes k :: "'a::len word"
  assumes szv: "sz < LENGTH('a)"
  and     kv:  "k < 2 ^ sz"
  shows   "unat k < 2 ^ sz"
  using szv unat_mono [OF kv] by simp

lemma unat_mult_power_lem:
  assumes kv: "k < 2 ^ (LENGTH('a::len) - sz)"
  shows "unat (2 ^ sz * of_nat k :: (('a::len) word)) = 2 ^ sz * k"
proof (cases \<open>sz < LENGTH('a)\<close>)
  case True
  with assms show ?thesis
    by (simp add: unat_word_ariths take_bit_eq_mod mod_simps unsigned_of_nat)
      (simp add: take_bit_nat_eq_self_iff nat_less_power_trans flip: take_bit_eq_mod)
next
  case False
  with assms show ?thesis
    by simp
qed

lemma word_plus_mcs_4:
  "\<lbrakk>v + x \<le> w + x; x \<le> v + x\<rbrakk> \<Longrightarrow> v \<le> (w::'a::len word)"
  by uint_arith

lemma word_plus_mcs_3:
  "\<lbrakk>v \<le> w; x \<le> w + x\<rbrakk> \<Longrightarrow> v + x \<le> w + (x::'a::len word)"
  by unat_arith

lemma word_le_minus_one_leq:
  "x < y \<Longrightarrow> x \<le> y - 1" for x :: "'a :: len word"
  by transfer (metis le_less_trans less_irrefl take_bit_decr_eq take_bit_nonnegative zle_diff1_eq)

lemma word_less_sub_le[simp]:
  fixes x :: "'a :: len word"
  assumes nv: "n < LENGTH('a)"
  shows "(x \<le> 2 ^ n - 1) = (x < 2 ^ n)"
  using le_less_trans word_le_minus_one_leq nv power_2_ge_iff by blast

lemma unat_of_nat_len:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x :: 'a::len word) = x"
  by (simp add: unsigned_of_nat take_bit_nat_eq_self_iff)

lemma unat_of_nat_eq:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x ::'a::len word) = x"
  by (rule unat_of_nat_len)

lemma unat_eq_of_nat:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat (x :: 'a::len word) = n) = (x = of_nat n)"
  by transfer
    (auto simp add: take_bit_of_nat nat_eq_iff take_bit_nat_eq_self_iff intro: sym)

lemma alignUp_div_helper:
  fixes a :: "'a::len word"
  assumes kv: "k < 2 ^ (LENGTH('a) - n)"
  and     xk: "x = 2 ^ n * of_nat k"
  and    le: "a \<le> x"
  and    sz: "n < LENGTH('a)"
  and   anz: "a mod 2 ^ n \<noteq> 0"
  shows "a div 2 ^ n < of_nat k"
proof -
  have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using xk kv sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst unat_power_lower, simp)
    apply (subst mult.commute)
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have "unat a div 2 ^ n * 2 ^ n \<noteq> unat a"
  proof -
    have "unat a = unat a div 2 ^ n * 2 ^ n + unat a mod 2 ^ n"
      by (simp add: div_mult_mod_eq)
    also have "\<dots> \<noteq> unat a div 2 ^ n * 2 ^ n" using sz anz
      by (simp add: unat_arith_simps)
    finally show ?thesis ..
  qed

  then have "a div 2 ^ n * 2 ^ n < a" using sz anz
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (subst unat_div)
    apply simp
    apply (rule order_le_less_trans [OF mod_less_eq_dividend])
    apply (erule order_le_neq_trans [OF div_mult_le])
    done

  also from xk le have "\<dots> \<le> of_nat k * 2 ^ n" by (simp add: field_simps)
  finally show ?thesis using sz kv
    apply -
    apply (erule word_mult_less_dest [OF _ _ kn])
    apply (simp add: unat_div)
    apply (rule order_le_less_trans [OF div_mult_le])
    apply (rule unat_lt2p)
    done
qed

lemma mask_out_sub_mask:
  "(x AND NOT (mask n)) = x - (x AND (mask n))"
  for x :: \<open>'a::len word\<close>
  by (fact and_not_eq_minus_and)

lemma subtract_mask:
  "p - (p AND mask n) = (p AND NOT (mask n))"
  "p - (p AND NOT (mask n)) = (p AND mask n)"
  for p :: \<open>'a::len word\<close>
  by (auto simp: and_not_eq_minus_and)

lemma take_bit_word_eq_self_iff:
  \<open>take_bit n w = w \<longleftrightarrow> n \<ge> LENGTH('a) \<or> w < 2 ^ n\<close>
  for w :: \<open>'a::len word\<close>
  using take_bit_int_eq_self_iff [of n \<open>take_bit LENGTH('a) (uint w)\<close>]
  by (transfer fixing: n) auto

lemma word_power_increasing:
  assumes x: "2 ^ x < (2 ^ y::'a::len word)" "x < LENGTH('a)" "y < LENGTH('a)"
  shows "x < y" using x
  using assms by transfer simp

lemma mask_twice:
  "(x AND mask n) AND mask m = x AND mask (min m n)"
  for x :: \<open>'a::len word\<close>
  by (simp flip: take_bit_eq_mask)

lemma plus_one_helper[elim!]:
  "x < n + (1 :: 'a :: len word) \<Longrightarrow> x \<le> n"
  apply (simp add: word_less_nat_alt word_le_nat_alt field_simps)
  apply (case_tac "1 + n = 0")
   apply simp_all
  apply (subst(asm) unatSuc, assumption)
  apply arith
  done

lemma plus_one_helper2:
  "\<lbrakk> x \<le> n; n + 1 \<noteq> 0 \<rbrakk> \<Longrightarrow> x < n + (1 :: 'a :: len word)"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps
                unatSuc)

lemma less_x_plus_1:
  "x \<noteq> - 1 \<Longrightarrow> (y < x + 1) = (y < x \<or> y = x)" for x :: "'a::len word"
  by (meson max_word_wrap plus_one_helper plus_one_helper2 word_le_less_eq)

lemma word_Suc_leq:
  fixes k::"'a::len word" shows "k \<noteq> - 1 \<Longrightarrow> x < k + 1 \<longleftrightarrow> x \<le> k"
  using less_x_plus_1 word_le_less_eq by auto

lemma word_Suc_le:
   fixes k::"'a::len word" shows "x \<noteq> - 1 \<Longrightarrow> x + 1 \<le> k \<longleftrightarrow> x < k"
  by (meson not_less word_Suc_leq)

lemma word_lessThan_Suc_atMost:
  \<open>{..< k + 1} = {..k}\<close> if \<open>k \<noteq> - 1\<close> for k :: \<open>'a::len word\<close>
  using that by (simp add: lessThan_def atMost_def word_Suc_leq)

lemma word_atLeastLessThan_Suc_atLeastAtMost:
  \<open>{l ..< u + 1} = {l..u}\<close> if \<open>u \<noteq> - 1\<close> for l :: \<open>'a::len word\<close>
  using that by (simp add: atLeastAtMost_def atLeastLessThan_def word_lessThan_Suc_atMost)

lemma word_atLeastAtMost_Suc_greaterThanAtMost:
  \<open>{m<..u} = {m + 1..u}\<close> if \<open>m \<noteq> - 1\<close> for m :: \<open>'a::len word\<close>
  using that by (simp add: greaterThanAtMost_def greaterThan_def atLeastAtMost_def atLeast_def word_Suc_le)

lemma word_atLeastLessThan_Suc_atLeastAtMost_union:
  fixes l::"'a::len word"
  assumes "m \<noteq> - 1" and "l \<le> m" and "m \<le> u"
  shows "{l..m} \<union> {m+1..u} = {l..u}"
proof -
  from ivl_disj_un_two(8)[OF assms(2) assms(3)] have "{l..u} = {l..m} \<union> {m<..u}" by blast
  with assms show ?thesis by(simp add: word_atLeastAtMost_Suc_greaterThanAtMost)
qed

lemma max_word_less_eq_iff [simp]:
  \<open>- 1 \<le> w \<longleftrightarrow> w = - 1\<close> for w :: \<open>'a::len word\<close>
  by (fact word_order.extremum_unique)

lemma word_or_zero:
  "(a OR b = 0) = (a = 0 \<and> b = 0)"
  for a b :: \<open>'a::len word\<close>
  by (fact or_eq_0_iff)

lemma word_2p_mult_inc:
  assumes x: "2 * 2 ^ n < (2::'a::len word) * 2 ^ m"
  assumes suc_n: "Suc n < LENGTH('a::len)"
  shows "2^n < (2::'a::len word)^m"
  by (smt suc_n le_less_trans lessI nat_less_le nat_mult_less_cancel_disj p2_gt_0
          power_Suc power_Suc unat_power_lower word_less_nat_alt x)

lemma power_overflow:
  "n \<ge> LENGTH('a) \<Longrightarrow> 2 ^ n = (0 :: 'a::len word)"
  by simp

lemmas extra_sle_sless_unfolds [simp] =
    word_sle_eq[where a=0 and b=1]
    word_sle_eq[where a=0 and b="numeral n"]
    word_sle_eq[where a=1 and b=0]
    word_sle_eq[where a=1 and b="numeral n"]
    word_sle_eq[where a="numeral n" and b=0]
    word_sle_eq[where a="numeral n" and b=1]
    word_sless_alt[where a=0 and b=1]
    word_sless_alt[where a=0 and b="numeral n"]
    word_sless_alt[where a=1 and b=0]
    word_sless_alt[where a=1 and b="numeral n"]
    word_sless_alt[where a="numeral n" and b=0]
    word_sless_alt[where a="numeral n" and b=1]
  for n

lemma word_sint_1:
  "sint (1::'a::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma ucast_of_nat:
  "is_down (ucast :: 'a :: len word \<Rightarrow> 'b :: len word)
    \<Longrightarrow> ucast (of_nat n :: 'a word) = (of_nat n :: 'b word)"
  by transfer simp

lemma scast_1':
  "(scast (1::'a::len word) :: 'b::len word) =
   (word_of_int (signed_take_bit (LENGTH('a::len) - Suc 0) (1::int)))"
  by transfer simp

lemma scast_1:
  "(scast (1::'a::len word) :: 'b::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma unat_minus_one_word:
  "unat (-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  by (simp add: mask_eq_exp_minus_1 unsigned_minus_1_eq_mask)

lemmas word_diff_ls'' = word_diff_ls [where xa=x and x=x for x]
lemmas word_diff_ls' = word_diff_ls'' [simplified]

lemmas word_l_diffs' = word_l_diffs [where xa=x and x=x for x]
lemmas word_l_diffs = word_l_diffs' [simplified]

lemma two_power_increasing:
  "\<lbrakk> n \<le> m; m < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n \<le> 2 ^ m"
  by (simp add: word_le_nat_alt)

lemma word_leq_le_minus_one:
  "\<lbrakk> x \<le> y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x - 1 < (y :: 'a :: len word)"
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst unat_minus_one)
   apply assumption
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma neg_mask_combine:
  "NOT(mask a) AND NOT(mask b) = NOT(mask (max a b) :: 'a::len word)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma neg_mask_twice:
  "x AND NOT(mask n) AND NOT(mask m) = x AND NOT(mask (max n m))"
  for x :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma multiple_mask_trivia:
  "n \<ge> m \<Longrightarrow> (x AND NOT(mask n)) + (x AND mask n AND NOT(mask m)) = x AND NOT(mask m)"
  for x :: \<open>'a::len word\<close>
  apply (rule trans[rotated], rule_tac w="mask n" in word_plus_and_or_coroll2)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs neg_mask_twice
                   max_absorb2)
  done

lemma word_of_nat_less:
  "\<lbrakk> n < unat x \<rbrakk> \<Longrightarrow> of_nat n < x"
  apply (simp add: word_less_nat_alt)
  apply (erule order_le_less_trans[rotated])
  apply (simp add: unsigned_of_nat take_bit_eq_mod)
  done

lemma unat_mask:
  "unat (mask n :: 'a :: len word) = 2 ^ (min n (LENGTH('a))) - 1"
  apply (subst min.commute)
  apply (simp add: mask_eq_decr_exp not_less min_def  split: if_split_asm)
  apply (intro conjI impI)
   apply (simp add: unat_sub_if_size)
   apply (simp add: power_overflow word_size)
  apply (simp add: unat_sub_if_size)
  done

lemma mask_over_length:
  "LENGTH('a) \<le> n \<Longrightarrow> mask n = (-1::'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma Suc_2p_unat_mask:
  "n < LENGTH('a) \<Longrightarrow> Suc (2 ^ n * k + unat (mask n :: 'a::len word)) = 2 ^ n * (k+1)"
  by (simp add: unat_mask)

lemma sint_of_nat_ge_zero:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) \<ge> 0"
  by (simp add: bit_iff_odd signed_of_nat)

lemma int_eq_sint:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) = int x"
  apply transfer
  apply (rule signed_take_bit_int_eq_self)
   apply simp_all
  apply (metis negative_zle numeral_power_eq_of_nat_cancel_iff)
  done

lemma sint_of_nat_le:
  "\<lbrakk> b < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk>
   \<Longrightarrow> sint (of_nat a :: 'a :: len word) \<le> sint (of_nat b :: 'a :: len word)"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply transfer
  apply (subst signed_take_bit_eq_if_positive)
   apply (simp add: bit_simps)
  apply (metis bit_take_bit_iff nat_less_le order_less_le_trans take_bit_nat_eq_self_iff)
  apply (subst signed_take_bit_eq_if_positive)
    apply (simp add: bit_simps)
  apply (metis bit_take_bit_iff nat_less_le take_bit_nat_eq_self_iff)
    apply (simp flip: of_nat_take_bit add: take_bit_nat_eq_self)
  done

lemma word_le_not_less:
  "((b::'a::len word) \<le> a) = (\<not>(a < b))"
  by fastforce

lemma less_is_non_zero_p1:
  fixes a :: "'a :: len word"
  shows "a < k \<Longrightarrow> a + 1 \<noteq> 0"
  apply (erule contrapos_pn)
  apply (drule max_word_wrap)
  apply (simp add: not_less)
  done

lemma unat_add_lem':
  "(unat x + unat y < 2 ^ LENGTH('a)) \<Longrightarrow>
    (unat (x + y :: 'a :: len word) = unat x + unat y)"
  by (subst unat_add_lem[symmetric], assumption)

lemma word_less_two_pow_divI:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (n - m); m \<le> n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply (rule order_le_less_trans [OF div_le_dividend])
   apply (rule unat_lt2p)
  apply (simp add: power_sub)
  done

lemma word_less_two_pow_divD:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ n div 2 ^ m \<rbrakk>
     \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (cases "n < LENGTH('a)")
   apply (cases "m < LENGTH('a)")
    apply (simp add: word_less_nat_alt)
    apply (subst(asm) unat_word_ariths)
    apply (subst(asm) mod_less)
     apply (rule order_le_less_trans [OF div_le_dividend])
     apply (rule unat_lt2p)
    apply (clarsimp dest!: less_two_pow_divD)
   apply (simp add: power_overflow)
   apply (simp add: word_div_def)
  apply (simp add: power_overflow word_div_def)
  done

lemma of_nat_less_two_pow_div_set:
  "\<lbrakk> n < LENGTH('a) \<rbrakk> \<Longrightarrow>
   {x. x < (2 ^ n div 2 ^ m :: 'a::len word)}
      = of_nat ` {k. k < 2 ^ n div 2 ^ m}"
  apply (simp add: image_def)
  apply (safe dest!: word_less_two_pow_divD less_two_pow_divD
             intro!: word_less_two_pow_divI)
   apply (rule_tac x="unat x" in exI)
   apply (simp add: power_sub[symmetric])
   apply (subst unat_power_lower[symmetric, where 'a='a])
    apply simp
   apply (erule unat_mono)
  apply (subst word_unat_power)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply assumption
  done

lemma ucast_less:
  "LENGTH('b) < LENGTH('a) \<Longrightarrow>
   (ucast (x :: 'b :: len word) :: ('a :: len word)) < 2 ^ LENGTH('b)"
  by transfer simp

lemma ucast_range_less:
  "LENGTH('a :: len) < LENGTH('b :: len) \<Longrightarrow>
   range (ucast :: 'a word \<Rightarrow> 'b word) = {x. x < 2 ^ len_of TYPE ('a)}"
  apply safe
   apply (erule ucast_less)
  apply (simp add: image_def)
  apply (rule_tac x="ucast x" in exI)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps)
  apply (metis bit_take_bit_iff take_bit_word_eq_self_iff)
  done

lemma word_power_less_diff:
  "\<lbrakk>2 ^ n * q < (2::'a::len word) ^ m; q < 2 ^ (LENGTH('a) - n)\<rbrakk> \<Longrightarrow> q < 2 ^ (m - n)"
  apply (case_tac "m \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (case_tac "n \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (cases "n = 0")
   apply simp
  apply (subst word_less_nat_alt)
  apply (subst unat_power_lower)
   apply simp
  apply (rule nat_power_less_diff)
  apply (simp add: word_less_nat_alt)
  apply (subst (asm) iffD1 [OF unat_mult_lem])
   apply (simp add:nat_less_power_trans)
  apply simp
  done

lemma word_less_sub_1:
  "x < (y :: 'a :: len word) \<Longrightarrow> x \<le> y - 1"
  by (fact word_le_minus_one_leq)

lemma word_sub_mono2:
  "\<lbrakk> a + b \<le> c + d; c \<le> a; b \<le> a + b; d \<le> c + d \<rbrakk> \<Longrightarrow> b \<le> (d :: 'a :: len word)"
  by (drule(1) word_sub_mono; simp)

lemma word_not_le:
  "(\<not> x \<le> (y :: 'a :: len word)) = (y < x)"
  by (fact not_le)

lemma word_subset_less:
  "\<lbrakk> {x .. x + r - 1} \<subseteq> {y .. y + s - 1};
     x \<le> x + r - 1; y \<le> y + (s :: 'a :: len word) - 1;
     s \<noteq> 0 \<rbrakk>
     \<Longrightarrow> r \<le> s"
  apply (frule subsetD[where c=x])
   apply simp
  apply (drule subsetD[where c="x + r - 1"])
   apply simp
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (drule(1) word_sub_mono2)
    apply (simp_all add: olen_add_eqv[symmetric])
  apply (erule word_le_minus_cancel)
  apply (rule ccontr)
  apply (simp add: word_not_le)
  done

lemma uint_power_lower:
  "n < LENGTH('a) \<Longrightarrow> uint (2 ^ n :: 'a :: len word) = (2 ^ n :: int)"
  by (rule uint_2p_alt)

lemma power_le_mono:
  "\<lbrakk>2 ^ n \<le> (2::'a::len word) ^ m; n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> n \<le> m"
  apply (clarsimp simp add: le_less)
  apply safe
  apply (simp add: word_less_nat_alt)
  apply (simp only: uint_arith_simps(3))
  apply (drule uint_power_lower)+
  apply simp
  done

lemma two_power_eq:
  "\<lbrakk>n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> ((2::'a::len word) ^ n = 2 ^ m) = (n = m)"
  apply safe
  apply (rule order_antisym)
   apply (simp add: power_le_mono[where 'a='a])+
  done

lemma unat_less_helper:
  "x < of_nat n \<Longrightarrow> unat x < n"
  apply (simp add: word_less_nat_alt)
  apply (erule order_less_le_trans)
  apply (simp add: take_bit_eq_mod unsigned_of_nat)
  done

lemma nat_uint_less_helper:
  "nat (uint y) = z \<Longrightarrow> x < y \<Longrightarrow> nat (uint x) < z"
  apply (erule subst)
  apply (subst unat_eq_nat_uint [symmetric])
  apply (subst unat_eq_nat_uint [symmetric])
  by (simp add: unat_mono)

lemma of_nat_0:
  "\<lbrakk>of_nat n = (0::'a::len word); n < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> n = 0"
  by (auto simp add: word_of_nat_eq_0_iff)

lemma of_nat_inj:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
   (of_nat x = (of_nat y :: 'a :: len word)) = (x = y)"
  by (metis unat_of_nat_len)

lemma div_to_mult_word_lt:
  "\<lbrakk> (x :: 'a :: len word) \<le> y div z \<rbrakk> \<Longrightarrow> x * z \<le> y"
  apply (cases "z = 0")
   apply simp
  apply (simp add: word_neq_0_conv)
  apply (rule order_trans)
   apply (erule(1) word_mult_le_mono1)
   apply (simp add: unat_div)
   apply (rule order_le_less_trans [OF div_mult_le])
   apply simp
  apply (rule word_div_mult_le)
  done

lemma ucast_ucast_mask:
  "(ucast :: 'a :: len word \<Rightarrow> 'b :: len word) (ucast x) = x AND mask (len_of TYPE ('a))"
  apply (simp flip: take_bit_eq_mask)
  apply transfer
  apply (simp add: ac_simps)
  done

lemma ucast_ucast_len:
  "\<lbrakk> x < 2 ^ LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (ucast x::'b::len word) = (x::'a::len word)"
  apply (subst ucast_ucast_mask)
  apply (erule less_mask_eq)
  done

lemma ucast_ucast_id:
  "LENGTH('a) < LENGTH('b) \<Longrightarrow> ucast (ucast (x::'a::len word)::'b::len word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)

lemma unat_ucast:
  "unat (ucast x :: ('a :: len) word) = unat x mod 2 ^ (LENGTH('a))"
proof -
  have \<open>2 ^ LENGTH('a) = nat (2 ^ LENGTH('a))\<close>
    by simp
  moreover have \<open>unat (ucast x :: 'a word) = unat x mod nat (2 ^ LENGTH('a))\<close>
    by transfer (simp flip: nat_mod_distrib take_bit_eq_mod)
  ultimately show ?thesis
    by (simp only:)
qed

lemma ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow>
   (ucast x < ((ucast (y :: 'a::len word)) :: 'b::len word)) = (x < y)"
  apply (simp add: word_less_nat_alt unat_ucast)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply simp
  done

\<comment> \<open>This weaker version was previously called @{text ucast_less_ucast}. We retain it to
    support existing proofs.\<close>
lemmas ucast_less_ucast_weak = ucast_less_ucast[OF order.strict_implies_order]

lemma unat_Suc2:
  fixes n :: "'a :: len word"
  shows
  "n \<noteq> -1 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  apply (subst add.commute, rule unatSuc)
  apply (subst eq_diff_eq[symmetric], simp add: minus_equation_iff)
  done

lemma word_div_1:
  "(n :: 'a :: len word) div 1 = n"
  by (fact bits_div_by_1)

lemma word_minus_one_le:
  "-1 \<le> (x :: 'a :: len word) = (x = -1)"
  by (fact word_order.extremum_unique)

lemma up_scast_inj:
  "\<lbrakk> scast x = (scast y :: 'b :: len word); size x \<le> LENGTH('b) \<rbrakk> \<Longrightarrow> x = y"
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>; simp)
  apply (metis order_refl take_bit_signed_take_bit take_bit_tightened)
  done

lemma up_scast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow>
  (scast x = (scast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_scast_inj simp: word_size)

lemma word_le_add:
  fixes x :: "'a :: len word"
  shows "x \<le> y \<Longrightarrow> \<exists>n. y = x + of_nat n"
  by (rule exI [where x = "unat (y - x)"]) simp

lemma word_plus_mcs_4':
  "\<lbrakk>x + v \<le> x + w; x \<le> x + v\<rbrakk> \<Longrightarrow> v \<le> w" for x :: "'a::len word"
  by (rule word_plus_mcs_4; simp add: add.commute)

lemma unat_eq_1:
  \<open>unat x = Suc 0 \<longleftrightarrow> x = 1\<close>
  by (auto intro!: unsigned_word_eqI [where ?'a = nat])

lemma word_unat_Rep_inject1:
  \<open>unat x = unat 1 \<longleftrightarrow> x = 1\<close>
  by (simp add: unat_eq_1)

lemma and_not_mask_twice:
  "(w AND NOT (mask n)) AND NOT (mask m) = w AND NOT (mask (max m n))"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma word_less_cases:
  "x < y \<Longrightarrow> x = y - 1 \<or> x < y - (1 ::'a::len word)"
  apply (drule word_less_sub_1)
  apply (drule order_le_imp_less_or_eq)
  apply auto
  done

lemma mask_and_mask:
  "mask a AND mask b = (mask (min a b) :: 'a::len word)"
  by (simp flip: take_bit_eq_mask ac_simps)

lemma mask_eq_0_eq_x:
  "(x AND w = 0) = (x AND NOT w = x)"
  for x w :: \<open>'a::len word\<close>
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma mask_eq_x_eq_0:
  "(x AND w = x) = (x AND NOT w = 0)"
  for x w :: \<open>'a::len word\<close>
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma compl_of_1: "NOT 1 = (-2 :: 'a :: len word)"
  by (fact not_one_eq)

lemma split_word_eq_on_mask:
  "(x = y) = (x AND m = y AND m \<and> x AND NOT m = y AND NOT m)"
  for x y m :: \<open>'a::len word\<close>
  apply transfer
  apply (simp add: bit_eq_iff)
  apply (auto simp add: bit_simps ac_simps)
  done

lemma word_FF_is_mask:
  "0xFF = (mask 8 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma word_1FF_is_mask:
  "0x1FF = (mask 9 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma ucast_of_nat_small:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> ucast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply transfer
  apply (auto simp add: take_bit_of_nat min_def not_le)
  apply (metis linorder_not_less min_def take_bit_nat_eq_self take_bit_take_bit)
  done

lemma word_le_make_less:
  fixes x :: "'a :: len word"
  shows "y \<noteq> -1 \<Longrightarrow> (x \<le> y) = (x < (y + 1))"
  apply safe
  apply (erule plus_one_helper2)
  apply (simp add: eq_diff_eq[symmetric])
  done

lemmas finite_word = finite [where 'a="'a::len word"]

lemma word_to_1_set:
  "{0 ..< (1 :: 'a :: len word)} = {0}"
  by fastforce

lemma word_leq_minus_one_le:
  fixes x :: "'a::len word"
  shows "\<lbrakk>y \<noteq> 0; x \<le> y - 1 \<rbrakk> \<Longrightarrow> x < y"
  using le_m1_iff_lt word_neq_0_conv by blast

lemma word_count_from_top:
  "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: 'a :: len word} = {0 ..< n - 1} \<union> {n - 1}"
  apply (rule set_eqI, rule iffI)
   apply simp
   apply (drule word_le_minus_one_leq)
   apply (rule disjCI)
   apply simp
  apply simp
  apply (erule word_leq_minus_one_le)
  apply fastforce
  done

lemma word_minus_one_le_leq:
  "\<lbrakk> x - 1 < y \<rbrakk> \<Longrightarrow> x \<le> (y :: 'a :: len word)"
  apply (cases "x = 0")
   apply simp
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst(asm) unat_minus_one)
   apply (simp add: word_less_nat_alt)
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma word_must_wrap:
  "\<lbrakk> x \<le> n - 1; n \<le> x \<rbrakk> \<Longrightarrow> n = (0 :: 'a :: len word)"
  using dual_order.trans sub_wrap word_less_1 by blast

lemma range_subset_card:
  "\<lbrakk> {a :: 'a :: len word .. b} \<subseteq> {c .. d}; b \<ge> a \<rbrakk> \<Longrightarrow> d \<ge> c \<and> d - c \<ge> b - a"
  using word_sub_le word_sub_mono by fastforce

lemma less_1_simp:
  "n - 1 < m = (n \<le> (m :: 'a :: len word) \<and> n \<noteq> 0)"
  by unat_arith

lemma word_power_mod_div:
  fixes x :: "'a::len word"
  shows "\<lbrakk> n < LENGTH('a); m < LENGTH('a)\<rbrakk>
  \<Longrightarrow> x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)"
  apply (simp add: word_arith_nat_div unat_mod power_mod_div)
  apply (subst unat_arith_simps(3))
  apply (subst unat_mod)
  apply (subst unat_of_nat)+
  apply (simp add: mod_mod_power min.commute)
  done

lemma word_range_minus_1':
  fixes a :: "'a :: len word"
  shows "a \<noteq> 0 \<Longrightarrow> {a - 1<..b} = {a..b}"
  by (simp add: greaterThanAtMost_def atLeastAtMost_def greaterThan_def atLeast_def less_1_simp)

lemma word_range_minus_1:
  fixes a :: "'a :: len word"
  shows "b \<noteq> 0 \<Longrightarrow> {a..b - 1} = {a..<b}"
  apply (simp add: atLeastLessThan_def atLeastAtMost_def atMost_def lessThan_def)
  apply (rule arg_cong [where f = "\<lambda>x. {a..} \<inter> x"])
  apply rule
   apply clarsimp
   apply (erule contrapos_pp)
   apply (simp add: linorder_not_less linorder_not_le word_must_wrap)
  apply (clarsimp)
  apply (drule word_le_minus_one_leq)
  apply (auto simp: word_less_sub_1)
  done

lemma ucast_nat_def:
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> 'b :: len word) x"
  by transfer simp

lemma overflow_plus_one_self:
  "(1 + p \<le> p) = (p = (-1 :: 'a :: len word))"
  apply rule
  apply (rule ccontr)
   apply (drule plus_one_helper2)
   apply (rule notI)
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
   apply (simp add: field_simps)
  apply simp
  done

lemma plus_1_less:
  "(x + 1 \<le> (x :: 'a :: len word)) = (x = -1)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (cut_tac plus_one_helper2[where x=x, OF order_refl])
    apply simp
   apply clarsimp
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply simp
  done

lemma pos_mult_pos_ge:
  "[|x > (0::int); n>=0 |] ==> n * x >= n*1"
  apply (simp only: mult_left_mono)
  done

lemma word_plus_strict_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y < z; x \<le> x + z\<rbrakk> \<Longrightarrow> x + y < x + z"
  by unat_arith

lemma word_div_mult:
  "0 < c \<Longrightarrow> a < b * c \<Longrightarrow> a div c < b" for a b c :: "'a::len word"
  by (rule classical)
     (use div_to_mult_word_lt [of b a c] in
      \<open>auto simp add: word_less_nat_alt word_le_nat_alt unat_div\<close>)

lemma word_less_power_trans_ofnat:
  "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> of_nat n * 2 ^ k < (2::'a::len word) ^ m"
  apply (subst mult.commute)
  apply (rule word_less_power_trans)
    apply (simp_all add: word_less_nat_alt unsigned_of_nat)
  using take_bit_nat_less_eq_self
  apply (rule le_less_trans)
  apply assumption
  done

lemma word_1_le_power:
  "n < LENGTH('a) \<Longrightarrow> (1 :: 'a :: len word) \<le> 2 ^ n"
  by (rule inc_le[where i=0, simplified], erule iffD2[OF p2_gt_0])

lemma unat_1_0:
  "1 \<le> (x::'a::len word) = (0 < unat x)"
  by (auto simp add: word_le_nat_alt)

lemma x_less_2_0_1':
  fixes x :: "'a::len word"
  shows "\<lbrakk>LENGTH('a) \<noteq> 1; x < 2\<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  apply (cases \<open>2 \<le> LENGTH('a)\<close>; simp)
  apply transfer
  apply clarsimp
  apply (metis add.commute add.right_neutral even_two_times_div_two mod_div_trivial
               mod_pos_pos_trivial mult.commute mult_zero_left not_less not_take_bit_negative
               odd_two_times_div_two_succ)
  done

lemmas word_add_le_iff2 = word_add_le_iff [folded no_olen_add_nat]

lemma of_nat_power:
  shows "\<lbrakk> p < 2 ^ x; x < len_of TYPE ('a) \<rbrakk> \<Longrightarrow> of_nat p < (2 :: 'a :: len word) ^ x"
  apply (rule order_less_le_trans)
   apply (rule of_nat_mono_maybe)
    apply (erule power_strict_increasing)
    apply simp
   apply assumption
  apply (simp add: word_unat_power del: of_nat_power)
  done

lemma of_nat_n_less_equal_power_2:
  "n < LENGTH('a::len) \<Longrightarrow> ((of_nat n)::'a word) < 2 ^ n"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (metis of_nat_power n_less_equal_power_2 of_nat_Suc power_Suc)
  done

lemma eq_mask_less:
  fixes w :: "'a::len word"
  assumes eqm: "w = w AND mask n"
  and      sz: "n < len_of TYPE ('a)"
  shows "w < (2::'a word) ^ n"
  by (subst eqm, rule and_mask_less' [OF sz])

lemma of_nat_mono_maybe':
  fixes Y :: "nat"
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  assumes ylt: "y < 2 ^ len_of TYPE ('a)"
  shows   "(y < x) = (of_nat y < (of_nat x :: 'a :: len word))"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (rule ylt)
  apply (subst mod_less)
   apply (rule xlt)
  apply simp
  done

lemma of_nat_mono_maybe_le:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
  (y \<le> x) = ((of_nat y :: 'a :: len word) \<le> of_nat x)"
  apply (clarsimp simp: le_less)
  apply (rule disj_cong)
   apply (rule of_nat_mono_maybe', assumption+)
  apply auto
  using of_nat_inj apply blast
  done

lemma mask_AND_NOT_mask:
  "(w AND NOT (mask n)) AND mask n = 0"
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma AND_NOT_mask_plus_AND_mask_eq:
  "(w AND NOT (mask n)) + (w AND mask n) = w"
  for w :: \<open>'a::len word\<close>
  apply (subst disjunctive_add)
  apply (auto simp add: bit_simps)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps)
  done

lemma mask_eqI:
  fixes x :: "'a :: len word"
  assumes m1: "x AND mask n = y AND mask n"
  and     m2: "x AND NOT (mask n) = y AND NOT (mask n)"
  shows "x = y"
proof -
  have *: \<open>x = x AND mask n OR x AND NOT (mask n)\<close> for x :: \<open>'a word\<close>
    by (rule bit_word_eqI) (auto simp add: bit_simps)
  from assms * [of x] * [of y] show ?thesis
    by simp
qed

lemma neq_0_no_wrap:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<le> x + y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  by clarsimp

lemma unatSuc2:
  fixes n :: "'a :: len word"
  shows "n + 1 \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  by (simp add: add.commute unatSuc)

lemma word_of_nat_le:
  "n \<le> unat x \<Longrightarrow> of_nat n \<le> x"
  apply (simp add: word_le_nat_alt unat_of_nat)
  apply (erule order_trans[rotated])
  apply (simp add: take_bit_eq_mod)
  done

lemma word_unat_less_le:
  "a \<le> of_nat b \<Longrightarrow> unat a \<le> b"
  by (metis eq_iff le_cases le_unat_uoi word_of_nat_le)

lemma mask_Suc_0 : "mask (Suc 0) = (1 :: 'a::len word)"
  by (simp add: mask_eq_decr_exp)

lemma bool_mask':
  fixes x :: "'a :: len word"
  shows "2 < LENGTH('a) \<Longrightarrow> (0 < x AND 1) = (x AND 1 = 1)"
  by (simp add: and_one_eq mod_2_eq_odd)

lemma ucast_ucast_add:
  fixes x :: "'a :: len word"
  fixes y :: "'b :: len word"
  shows
  "LENGTH('b) \<ge> LENGTH('a) \<Longrightarrow>
    ucast (ucast x + y) = x + ucast y"
  apply transfer
  apply simp
  apply (subst (2) take_bit_add [symmetric])
  apply (subst take_bit_add [symmetric])
  apply simp
  done

lemma lt1_neq0:
  fixes x :: "'a :: len word"
  shows "(1 \<le> x) = (x \<noteq> 0)" by unat_arith

lemma word_plus_one_nonzero:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x \<le> x + y; y \<noteq> 0\<rbrakk> \<Longrightarrow> x + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (erule word_random)
  apply (simp add: lt1_neq0)
  done

lemma word_sub_plus_one_nonzero:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>n' \<le> n; n' \<noteq> 0\<rbrakk> \<Longrightarrow> (n - n') + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (rule word_random [where x' = n'])
   apply simp
   apply (erule word_sub_le)
  apply (simp add: lt1_neq0)
  done

lemma word_le_minus_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> z \<le> y; y \<le> x; z \<le> x \<rbrakk> \<Longrightarrow> x - y \<le> x - z"
  apply (rule word_sub_mono)
     apply simp
    apply assumption
   apply (erule word_sub_le)
  apply (erule word_sub_le)
  done

lemma word_0_sle_from_less:
  \<open>0 \<le>s x\<close> if \<open>x < 2 ^ (LENGTH('a) - 1)\<close> for x :: \<open>'a::len word\<close>
  using that
  apply transfer
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply (metis bit_take_bit_iff min_def nat_less_le not_less_eq take_bit_int_eq_self_iff take_bit_take_bit)
  done

lemma ucast_sub_ucast:
  fixes x :: "'a::len word"
  assumes "y \<le> x"
  assumes T: "LENGTH('a) \<le> LENGTH('b)"
  shows "ucast (x - y) = (ucast x - ucast y :: 'b::len word)"
proof -
  from T
  have P: "unat x < 2 ^ LENGTH('b)" "unat y < 2 ^ LENGTH('b)"
    by (fastforce intro!: less_le_trans[OF unat_lt2p])+
  then show ?thesis
    by (simp add: unat_arith_simps unat_ucast assms[simplified unat_arith_simps])
qed

lemma word_1_0:
  "\<lbrakk>a + (1::('a::len) word) \<le> b; a < of_nat x\<rbrakk> \<Longrightarrow> a < b"
  apply transfer
  apply (subst (asm) take_bit_incr_eq)
   apply (auto simp add: diff_less_eq)
  using take_bit_int_less_exp le_less_trans by blast

lemma unat_of_nat_less:"\<lbrakk> a < b; unat b = c \<rbrakk> \<Longrightarrow> a < of_nat c"
  by fastforce

lemma word_le_plus_1: "\<lbrakk> (y::('a::len) word) < y + n; a < n \<rbrakk> \<Longrightarrow> y + a \<le> y + a + 1"
  by unat_arith

lemma word_le_plus:"\<lbrakk>(a::('a::len) word) < a + b; c < b\<rbrakk> \<Longrightarrow> a \<le> a + c"
  by (metis order_less_imp_le word_random)

lemma sint_minus1 [simp]: "(sint x = -1) = (x = -1)"
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply transfer
  apply (simp only: flip: signed_take_bit_eq_iff_take_bit_eq)
  apply simp
  done

lemma sint_0 [simp]: "(sint x = 0) = (x = 0)"
  by (fact signed_eq_0_iff)

(* It is not always that case that "sint 1 = 1", because of 1-bit word sizes.
 * This lemma produces the different cases. *)
lemma sint_1_cases:
  P if \<open>\<lbrakk> len_of TYPE ('a::len) = 1; (a::'a word) = 0; sint a = 0 \<rbrakk> \<Longrightarrow> P\<close>
     \<open>\<lbrakk> len_of TYPE ('a) = 1; a = 1; sint (1 :: 'a word) = -1 \<rbrakk> \<Longrightarrow> P\<close>
     \<open>\<lbrakk> len_of TYPE ('a) > 1; sint (1 :: 'a word) = 1 \<rbrakk> \<Longrightarrow> P\<close>
proof (cases \<open>LENGTH('a) = 1\<close>)
  case True
  then have \<open>a = 0 \<or> a = 1\<close>
    by transfer auto
  with True that show ?thesis
    by auto
next
  case False
  with that show ?thesis
    by (simp add: less_le Suc_le_eq)
qed

lemma sint_int_min:
  "sint (- (2 ^ (LENGTH('a) - Suc 0)) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply transfer
  apply (simp add: signed_take_bit_int_eq_self)
  done

lemma sint_int_max_plus_1:
  "sint (2 ^ (LENGTH('a) - Suc 0) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp_all
  apply (subst word_of_int_2p [symmetric])
  apply (subst int_word_sint)
  apply simp
  done

lemma uint_range':
  \<open>0 \<le> uint x \<and> uint x < 2 ^ LENGTH('a)\<close>
  for x :: \<open>'a::len word\<close>
  by transfer simp

lemma sint_of_int_eq:
  "\<lbrakk> - (2 ^ (LENGTH('a) - 1)) \<le> x; x < 2 ^ (LENGTH('a) - 1) \<rbrakk> \<Longrightarrow> sint (of_int x :: ('a::len) word) = x"
  by (simp add: signed_take_bit_int_eq_self signed_of_int)

lemma of_int_sint:
  "of_int (sint a) = a"
  by simp

lemma sint_ucast_eq_uint:
    "\<lbrakk> \<not> is_down (ucast :: ('a::len word \<Rightarrow> 'b::len word)) \<rbrakk>
            \<Longrightarrow> sint ((ucast :: ('a::len word \<Rightarrow> 'b::len word)) x) = uint x"
  apply transfer
  apply (simp add: signed_take_bit_take_bit)
  done

lemma word_less_nowrapI':
  "(x :: 'a :: len word) \<le> z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  by uint_arith

lemma mask_plus_1:
  "mask n + 1 = (2 ^ n :: 'a::len word)"
  by (clarsimp simp: mask_eq_decr_exp)

lemma unat_inj: "inj unat"
  by (metis eq_iff injI word_le_nat_alt)

lemma unat_ucast_upcast:
  "is_up (ucast :: 'b word \<Rightarrow> 'a word)
      \<Longrightarrow> unat (ucast x :: ('a::len) word) = unat (x :: ('b::len) word)"
  unfolding ucast_eq unat_eq_nat_uint
  apply transfer
  apply simp
  done

lemma ucast_mono:
  "\<lbrakk> (x :: 'b :: len word) < y; y < 2 ^ LENGTH('a) \<rbrakk>
   \<Longrightarrow> ucast x < ((ucast y) :: 'a :: len word)"
  apply (simp only: flip: ucast_nat_def)
  apply (rule of_nat_mono_maybe)
  apply (rule unat_less_helper)
  apply simp
  apply (simp add: word_less_nat_alt)
  done

lemma ucast_mono_le:
  "\<lbrakk>x \<le> y; y < 2 ^ LENGTH('b)\<rbrakk> \<Longrightarrow> (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> ucast y"
  apply (simp only: flip: ucast_nat_def)
  apply (subst of_nat_mono_maybe_le[symmetric])
    apply (rule unat_less_helper)
    apply simp
   apply (rule unat_less_helper)
   apply (erule le_less_trans)
  apply (simp_all add: word_le_nat_alt)
  done

lemma ucast_mono_le':
  "\<lbrakk> unat y < 2 ^ LENGTH('b); LENGTH('b::len) < LENGTH('a::len); x \<le> y \<rbrakk>
   \<Longrightarrow> ucast x \<le> (ucast y :: 'b word)" for x y :: \<open>'a::len word\<close>
  by (auto simp: word_less_nat_alt intro: ucast_mono_le)

lemma neg_mask_add_mask:
  "((x:: 'a :: len word) AND NOT (mask n)) + (2 ^ n - 1) = x OR mask n"
  unfolding mask_2pm1 [symmetric]
  apply (subst word_plus_and_or_coroll; rule bit_word_eqI)
   apply (auto simp add: bit_simps)
  done

lemma le_step_down_word:"\<lbrakk>(i::('a::len) word) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by unat_arith

lemma le_step_down_word_2:
  fixes x :: "'a::len word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (subst (asm) word_le_less_eq,
      clarsimp,
      simp add: word_le_minus_one_leq)

lemma NOT_mask_AND_mask[simp]: "(w AND mask n) AND NOT (mask n) = 0"
  by (rule bit_eqI) (simp add: bit_simps)

lemma and_and_not[simp]:"(a AND b) AND NOT b = 0"
  for a b :: \<open>'a::len word\<close>
  apply (subst word_bw_assocs(1))
  apply clarsimp
  done

lemma ex_mask_1[simp]: "(\<exists>x. mask x = (1 :: 'a::len word))"
  apply (rule_tac x=1 in exI)
  apply (simp add:mask_eq_decr_exp)
  done

lemma not_switch:"NOT a = x \<Longrightarrow> a = NOT x"
  by auto

lemma test_bit_eq_iff: "bit u = bit v \<longleftrightarrow> u = v"
  for u v :: "'a::len word"
  by (auto intro: bit_eqI simp add: fun_eq_iff)

lemma test_bit_size: "bit w n \<Longrightarrow> n < size w"
  for w :: "'a::len word"
  by transfer simp

lemma word_eq_iff: "x = y \<longleftrightarrow> (\<forall>n<LENGTH('a). bit x n = bit y n)"
  for x y :: "'a::len word"
  by transfer (auto simp add: bit_eq_iff bit_take_bit_iff)

lemma word_eqI: "(\<And>n. n < size u \<longrightarrow> bit u n = bit v n) \<Longrightarrow> u = v"
  for u :: "'a::len word"
  by (simp add: word_size word_eq_iff)

lemma word_eqD: "u = v \<Longrightarrow> bit u x = bit v x"
  for u v :: "'a::len word"
  by simp

lemma test_bit_bin': "bit w n \<longleftrightarrow> n < size w \<and> bit (uint w) n"
  by transfer (simp add: bit_take_bit_iff)

lemmas test_bit_bin = test_bit_bin' [unfolded word_size]

lemma word_test_bit_def:
  \<open>bit a = bit (uint a)\<close>
  by transfer (simp add: fun_eq_iff bit_take_bit_iff)

lemmas test_bit_def' = word_test_bit_def [THEN fun_cong]

lemma word_test_bit_transfer [transfer_rule]:
  "(rel_fun pcr_word (rel_fun (=) (=)))
    (\<lambda>x n. n < LENGTH('a) \<and> bit x n) (bit :: 'a::len word \<Rightarrow> _)"
  by transfer_prover

lemma test_bit_wi:
  "bit (word_of_int x :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> bit x n"
  by transfer simp

lemma word_ops_nth_size:
  "n < size x \<Longrightarrow>
    bit (x OR y) n = (bit x n | bit y n) \<and>
    bit (x AND y) n = (bit x n \<and> bit y n) \<and>
    bit (x XOR y) n = (bit x n \<noteq> bit y n) \<and>
    bit (NOT x) n = (\<not> bit x n)"
  for x :: "'a::len word"
  by transfer (simp add: bit_or_iff bit_and_iff bit_xor_iff bit_not_iff)

lemma word_ao_nth:
  "bit (x OR y) n = (bit x n | bit y n) \<and>
    bit (x AND y) n = (bit x n \<and> bit y n)"
  for x :: "'a::len word"
  by transfer (auto simp add: bit_or_iff bit_and_iff)

lemmas lsb0 = len_gt_0 [THEN word_ops_nth_size [unfolded word_size]]

lemma nth_sint:
  fixes w :: "'a::len word"
  defines "l \<equiv> LENGTH('a)"
  shows "bit (sint w) n = (if n < l - 1 then bit w n else bit w (l - 1))"
  unfolding sint_uint l_def
  by (auto simp: bit_signed_take_bit_iff word_test_bit_def not_less min_def)

lemma test_bit_2p: "bit (word_of_int (2 ^ n)::'a::len word) m \<longleftrightarrow> m = n \<and> m < LENGTH('a)"
  by transfer (auto simp add: bit_exp_iff)

lemma nth_w2p: "bit ((2::'a::len word) ^ n) m \<longleftrightarrow> m = n \<and> m < LENGTH('a::len)"
  by transfer (auto simp add: bit_exp_iff)

lemma bang_is_le: "bit x m \<Longrightarrow> 2 ^ m \<le> x"
  for x :: "'a::len word"
  apply (rule xtrans(3))
   apply (rule_tac [2] y = "x" in le_word_or2)
  apply (rule word_eqI)
  apply (auto simp add: word_ao_nth nth_w2p word_size)
  done

lemmas msb0 = len_gt_0 [THEN diff_Suc_less, THEN word_ops_nth_size [unfolded word_size]]
lemmas msb1 = msb0 [where i = 0]

lemma test_bit_1 [iff]: "bit (1 :: 'a::len word) n \<longleftrightarrow> n = 0"
  by transfer (auto simp add: bit_1_iff)

lemma nth_0: "\<not> bit (0 :: 'a::len word) n"
  by transfer simp

lemma nth_minus1: "bit (-1 :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a)"
  by transfer simp

lemma nth_ucast_weak:
  "bit (ucast w::'a::len word) n = (bit w n \<and> n < LENGTH('a))"
  by transfer (simp add: bit_take_bit_iff ac_simps)

lemma nth_ucast:
  "bit (ucast (w::'a::len word)::'b::len word) n =
   (bit w n \<and> n < min LENGTH('a) LENGTH('b))"
  by (auto simp: not_le nth_ucast_weak dest: bit_imp_le_length)

lemma nth_mask:
  \<open>bit (mask n :: 'a::len word) i \<longleftrightarrow> i < n \<and> i < size (mask n :: 'a word)\<close>
  by (auto simp add: word_size Word.bit_mask_iff)

lemma nth_slice: "bit (slice n w :: 'a::len word) m = (bit w (m + n) \<and> m < LENGTH('a))"
  apply (auto simp add: bit_simps less_diff_conv dest: bit_imp_le_length)
  using bit_imp_le_length
  apply fastforce
  done

lemma test_bit_cat [OF refl]:
  "wc = word_cat a b \<Longrightarrow> bit wc n = (n < size wc \<and>
    (if n < size b then bit b n else bit a (n - size b)))"
  apply (simp add: word_size not_less; transfer)
       apply (auto simp add: bit_concat_bit_iff bit_take_bit_iff)
  done

\<comment> \<open>keep quantifiers for use in simplification\<close>
lemma test_bit_split':
  "word_split c = (a, b) \<longrightarrow>
    (\<forall>n m.
      bit b n = (n < size b \<and> bit c n) \<and>
      bit a m = (m < size a \<and> bit c (m + size b)))"
  by (auto simp add: word_split_bin' bit_unsigned_iff word_size bit_drop_bit_eq ac_simps
           dest: bit_imp_le_length)

lemma test_bit_split:
  "word_split c = (a, b) \<Longrightarrow>
    (\<forall>n::nat. bit b n \<longleftrightarrow> n < size b \<and> bit c n) \<and>
    (\<forall>m::nat. bit a m \<longleftrightarrow> m < size a \<and> bit c (m + size b))"
  by (simp add: test_bit_split')

lemma test_bit_split_eq:
  "word_split c = (a, b) \<longleftrightarrow>
    ((\<forall>n::nat. bit b n = (n < size b \<and> bit c n)) \<and>
     (\<forall>m::nat. bit a m = (m < size a \<and> bit c (m + size b))))"
  apply (rule_tac iffI)
   apply (rule_tac conjI)
    apply (erule test_bit_split [THEN conjunct1])
   apply (erule test_bit_split [THEN conjunct2])
  apply (case_tac "word_split c")
  apply (frule test_bit_split)
  apply (erule trans)
  apply (fastforce intro!: word_eqI simp add: word_size)
  done

lemma test_bit_rcat:
  "sw = size (hd wl) \<Longrightarrow> rc = word_rcat wl \<Longrightarrow> bit rc n =
    (n < size rc \<and> n div sw < size wl \<and> bit ((rev wl) ! (n div sw)) (n mod sw))"
  for wl :: "'a::len word list"
  by (simp add: word_size word_rcat_def rev_map bit_horner_sum_uint_exp_iff bit_simps not_le)

lemmas test_bit_cong = arg_cong [where f = "bit", THEN fun_cong]

lemma max_test_bit: "bit (- 1::'a::len word) n \<longleftrightarrow> n < LENGTH('a)"
  by (fact nth_minus1)

lemma map_nth_0 [simp]: "map (bit (0::'a::len word)) xs = replicate (length xs) False"
  by (simp flip: map_replicate_const)

lemma word_and_1:
  "n AND 1 = (if bit n 0 then 1 else 0)" for n :: "_ word"
  by (rule bit_word_eqI) (auto simp add: bit_and_iff bit_1_iff intro: gr0I)

lemma test_bit_1':
  "bit (1 :: 'a :: len word) n \<longleftrightarrow> 0 < LENGTH('a) \<and> n = 0"
  by simp

lemma nth_w2p_same:
  "bit (2^n :: 'a :: len word) n = (n < LENGTH('a))"
  by (simp add: nth_w2p)

lemma word_leI:
  "(\<And>n.  \<lbrakk>n < size (u::'a::len word); bit u n \<rbrakk> \<Longrightarrow> bit (v::'a::len word) n) \<Longrightarrow> u <= v"
  apply (rule order_trans [of u \<open>u AND v\<close> v])
   apply (rule eq_refl)
   apply (rule bit_word_eqI)
   apply (auto simp add: bit_simps word_and_le1 word_size)
  done

lemma bang_eq:
  fixes x :: "'a::len word"
  shows "(x = y) = (\<forall>n. bit x n = bit y n)"
  by (auto intro!: bit_eqI)

lemma neg_mask_test_bit:
  "bit (NOT(mask n) :: 'a :: len word) m = (n \<le> m \<and> m < LENGTH('a))"
  by (auto simp add: bit_simps)

lemma upper_bits_unset_is_l2p:
  \<open>(\<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> bit p n') \<longleftrightarrow> (p < 2 ^ n)\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
    if \<open>n < LENGTH('a)\<close>
    for p :: "'a :: len word"
proof
  assume ?Q
  then show ?P
    by (meson bang_is_le le_less_trans not_le word_power_increasing)
next
  assume ?P
  have \<open>take_bit n p = p\<close>
  proof (rule bit_word_eqI)
    fix q
    assume \<open>q < LENGTH('a)\<close>
    show \<open>bit (take_bit n p) q \<longleftrightarrow> bit p q\<close>
    proof (cases \<open>q < n\<close>)
      case True
      then show ?thesis
        by (auto simp add: bit_simps)
    next
      case False
      then have \<open>n \<le> q\<close>
        by simp
      with \<open>?P\<close> \<open>q < LENGTH('a)\<close> have \<open>\<not> bit p q\<close>
        by simp
      then show ?thesis
        by (simp add: bit_simps)
    qed
  qed
  with that show ?Q
    using take_bit_word_eq_self_iff [of n p] by auto
qed

lemma less_2p_is_upper_bits_unset:
  "p < 2 ^ n \<longleftrightarrow> n < LENGTH('a) \<and> (\<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> bit p n')" for p :: "'a :: len word"
  by (meson le_less_trans le_mask_iff_lt_2n upper_bits_unset_is_l2p word_zero_le)

lemma test_bit_over:
  "n \<ge> size (x::'a::len word) \<Longrightarrow> (bit x n) = False"
  by transfer auto

lemma le_mask_high_bits:
  "w \<le> mask n \<longleftrightarrow> (\<forall>i \<in> {n ..< size w}. \<not> bit w i)"
  for w :: \<open>'a::len word\<close>
  apply (auto simp add: bit_simps word_size less_eq_mask_iff_take_bit_eq_self)
   apply (metis bit_take_bit_iff leD)
  apply (metis atLeastLessThan_iff leI take_bit_word_eq_self_iff upper_bits_unset_is_l2p)
  done

lemma test_bit_conj_lt:
  "(bit x m \<and> m < LENGTH('a)) = bit x m" for x :: "'a :: len word"
  using test_bit_bin by blast

lemma neg_test_bit:
  "bit (NOT x) n = (\<not> bit x n \<and> n < LENGTH('a))" for x :: "'a::len word"
  by (cases "n < LENGTH('a)") (auto simp add: test_bit_over word_ops_nth_size word_size)

lemma nth_bounded:
  "\<lbrakk>bit (x :: 'a :: len word) n; x < 2 ^ m; m \<le> len_of TYPE ('a)\<rbrakk> \<Longrightarrow> n < m"
  apply (rule ccontr)
  apply (auto simp add: not_less)
  apply (meson bit_imp_le_length bit_uint_iff less_2p_is_upper_bits_unset test_bit_bin)
  done

lemma and_neq_0_is_nth:
  \<open>x AND y \<noteq> 0 \<longleftrightarrow> bit x n\<close> if \<open>y = 2 ^ n\<close> for x y :: \<open>'a::len word\<close>
  apply (simp add: bit_eq_iff bit_simps)
  using that apply (simp add: bit_simps not_le)
  apply transfer
  apply auto
  done

lemma nth_is_and_neq_0:
  "bit (x::'a::len word) n = (x AND 2 ^ n \<noteq> 0)"
  by (subst and_neq_0_is_nth; rule refl)

lemma max_word_not_less [simp]:
   "\<not> - 1 < x" for x :: \<open>'a::len word\<close>
  by (fact word_order.extremum_strict)

lemma bit_twiddle_min:
  "(y::'a::len word) XOR (((x::'a::len word) XOR y) AND (if x < y then -1 else 0)) = min x y"
  by (rule bit_eqI) (auto simp add: bit_simps)

lemma bit_twiddle_max:
  "(x::'a::len word) XOR (((x::'a::len word) XOR y) AND (if x < y then -1 else 0)) = max x y"
  by (rule bit_eqI) (auto simp add: bit_simps max_def)

lemma swap_with_xor:
  "\<lbrakk>(x::'a::len word) = a XOR b; y = b XOR x; z = x XOR y\<rbrakk> \<Longrightarrow> z = b \<and> y = a"
  by (auto intro: bit_word_eqI simp add: bit_simps)

lemma le_mask_imp_and_mask:
  "(x::'a::len word) \<le> mask n \<Longrightarrow> x AND mask n = x"
  by (metis and_mask_eq_iff_le_mask)

lemma or_not_mask_nop:
  "((x::'a::len word) OR NOT (mask n)) AND mask n = x AND mask n"
  by (metis word_and_not word_ao_dist2 word_bw_comms(1) word_log_esimps(3))

lemma mask_subsume:
  "\<lbrakk>n \<le> m\<rbrakk> \<Longrightarrow> ((x::'a::len word) OR y AND mask n) AND NOT (mask m) = x AND NOT (mask m)"
  by (rule bit_word_eqI) (auto simp add: bit_simps word_size)

lemma and_mask_0_iff_le_mask:
  fixes w :: "'a::len word"
  shows "(w AND NOT(mask n) = 0) = (w \<le> mask n)"
  by (simp add: mask_eq_0_eq_x le_mask_imp_and_mask and_mask_eq_iff_le_mask)

lemma mask_twice2:
  "n \<le> m \<Longrightarrow> ((x::'a::len word) AND mask m) AND mask n = x AND mask n"
  by (metis mask_twice min_def)

lemma uint_2_id:
  "LENGTH('a) \<ge> 2 \<Longrightarrow> uint (2::('a::len) word) = 2"
  by simp

lemma div_of_0_id[simp]:"(0::('a::len) word) div n = 0"
  by (simp add: word_div_def)

lemma degenerate_word:"LENGTH('a) = 1 \<Longrightarrow> (x::('a::len) word) = 0 \<or> x = 1"
  by (metis One_nat_def less_irrefl_nat sint_1_cases)

lemma div_by_0_word: "(x::'a::len word) div 0 = 0"
  by (fact bits_div_by_0)

lemma div_less_dividend_word:"\<lbrakk>x \<noteq> 0; n \<noteq> 1\<rbrakk> \<Longrightarrow> (x::('a::len) word) div n < x"
  apply (cases \<open>n = 0\<close>)
   apply clarsimp
   apply (simp add:word_neq_0_conv)
  apply (subst word_arith_nat_div)
  apply (rule word_of_nat_less)
  apply (rule div_less_dividend)
  using unat_eq_zero word_unat_Rep_inject1 apply force
  apply (simp add:unat_gt_0)
  done

lemma word_less_div:
  fixes x :: "('a::len) word"
    and y :: "('a::len) word"
  shows "x div y = 0 \<Longrightarrow> y = 0 \<or> x < y"
  apply (case_tac "y = 0", clarsimp+)
  by (metis One_nat_def Suc_le_mono le0 le_div_geq not_less unat_0 unat_div unat_gt_0 word_less_nat_alt zero_less_one)

lemma not_degenerate_imp_2_neq_0:"LENGTH('a) > 1 \<Longrightarrow> (2::('a::len) word) \<noteq> 0"
  by (metis numerals(1) power_not_zero power_zero_numeral)

lemma word_overflow:"(x::('a::len) word) + 1 > x \<or> x + 1 = 0"
  apply clarsimp
  by (metis diff_0 eq_diff_eq less_x_plus_1)

lemma word_overflow_unat:"unat ((x::('a::len) word) + 1) = unat x + 1 \<or> x + 1 = 0"
  by (metis Suc_eq_plus1 add.commute unatSuc)

lemma even_word_imp_odd_next:"even (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> odd (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma odd_word_imp_even_next:"odd (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> even (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma overflow_imp_lsb:"(x::('a::len) word) + 1 = 0 \<Longrightarrow> bit x 0"
  using even_plus_one_iff [of x] by (simp add: bit_0)

lemma odd_iff_lsb:"odd (unat (x::('a::len) word)) = bit x 0"
  by transfer (simp add: even_nat_iff bit_0)

lemma of_nat_neq_iff_word:
      "x mod 2 ^ LENGTH('a) \<noteq> y mod 2 ^ LENGTH('a) \<Longrightarrow>
         (((of_nat x)::('a::len) word) \<noteq> of_nat y) = (x \<noteq> y)"
  apply (rule iffI)
   apply (case_tac "x = y")
   apply (subst (asm) of_nat_eq_iff[symmetric])
   apply auto
  apply (case_tac "((of_nat x)::('a::len) word) = of_nat y")
  apply auto
   apply (metis unat_of_nat)
  done

lemma lsb_this_or_next: "\<not> (bit ((x::('a::len) word) + 1) 0) \<Longrightarrow> bit x 0"
  by (simp add: bit_0)

lemma mask_or_not_mask:
  "x AND mask n OR x AND NOT (mask n) = x"
  for x :: \<open>'a::len word\<close>
  apply (subst word_oa_dist, simp)
  apply (subst word_oa_dist2, simp)
  done

lemma word_gr0_conv_Suc: "(m::'a::len word) > 0 \<Longrightarrow> \<exists>n. m = n + 1"
  by (metis add.commute add_minus_cancel)

lemma revcast_down_us [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (signed_drop_bit n w)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps ac_simps)
  done

lemma revcast_down_ss [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (signed_drop_bit n w)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps ac_simps)
  done

lemma revcast_down_uu [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (drop_bit n w)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps ac_simps)
  done

lemma revcast_down_su [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (drop_bit n w)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps ac_simps)
  done

lemma cast_down_rev [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> uc w = revcast (push_bit n w)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps)
  done

lemma revcast_up [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow>
    rc w = push_bit n (ucast w :: 'a::len word)"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_simps)
  apply auto
  apply (metis add.commute add_diff_cancel_right)
  apply (metis diff_add_inverse2 diff_diff_add)
  done

lemmas rc1 = revcast_up [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]
lemmas rc2 = revcast_down_uu [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]

lemma word_ops_nth:
  fixes x y :: \<open>'a::len word\<close>
  shows
  word_or_nth:  "bit (x OR y) n = (bit x n \<or> bit y n)" and
  word_and_nth: "bit (x AND y) n = (bit x n \<and> bit y n)" and
  word_xor_nth: "bit (x XOR y) n = (bit x n \<noteq> bit y n)"
  by (simp_all add: bit_simps)

lemma word_power_nonzero:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (LENGTH('a) - n); n < LENGTH('a); x \<noteq> 0 \<rbrakk>
  \<Longrightarrow> x * 2 ^ n \<noteq> 0"
  by (metis Word.word_div_mult bits_div_0 len_gt_0 len_of_finite_2_def nat_mult_power_less_eq
    p2_gt_0 unat_mono unat_power_lower word_gt_a_gt_0)

lemma less_1_helper:
  "n \<le> m \<Longrightarrow> (n - 1 :: int) < m"
  by arith

lemma div_power_helper:
  "\<lbrakk> x \<le> y; y < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 ^ y - 1) div (2 ^ x :: 'a::len word) = 2 ^ (y - x) - 1"
  apply (simp flip: mask_eq_exp_minus_1 drop_bit_eq_div)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps not_le)
  done

lemma max_word_mask:
  "(- 1 :: 'a::len word) = mask LENGTH('a)"
  by (fact minus_1_eq_mask)

lemmas mask_len_max = max_word_mask[symmetric]

lemma mask_out_first_mask_some:
  "\<lbrakk> x AND NOT (mask n) = y; n \<le> m \<rbrakk> \<Longrightarrow> x AND NOT (mask m) = y AND NOT (mask m)"
  for x y :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps word_size)

lemma mask_lower_twice:
  "n \<le> m \<Longrightarrow> (x AND NOT (mask n)) AND NOT (mask m) = x AND NOT (mask m)"
  for x :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps word_size)

lemma mask_lower_twice2:
  "(a AND NOT (mask n)) AND NOT (mask m) = a AND NOT (mask (max n m))"
  for a :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma ucast_and_neg_mask:
  "ucast (x AND NOT (mask n)) = ucast x AND NOT (mask n)"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma ucast_and_mask:
  "ucast (x AND mask n) = ucast x AND mask n"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma ucast_mask_drop:
  "LENGTH('a :: len) \<le> n \<Longrightarrow> (ucast (x AND mask n) :: 'a word) = ucast x"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma mask_exceed:
  "n \<ge> LENGTH('a) \<Longrightarrow> (x::'a::len word) AND NOT (mask n) = 0"
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma word_add_no_overflow:"(x::'a::len word) < - 1 \<Longrightarrow> x < x + 1"
  using less_x_plus_1 order_less_le by blast

lemma lt_plus_1_le_word:
  fixes x :: "'a::len word"
  assumes bound:"n < unat (maxBound::'a word)"
  shows "x < 1 + of_nat n = (x \<le> of_nat n)"
  by (metis add.commute bound max_word_max word_Suc_leq word_not_le word_of_nat_less)

lemma unat_ucast_up_simp:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "unat (ucast x :: 'b::len word) = unat x"
  apply (rule bit_eqI)
  using assms apply (auto simp add: bit_simps dest: bit_imp_le_length)
  done

lemma unat_ucast_less_no_overflow:
  "\<lbrakk>n < 2 ^ LENGTH('a); unat f < n\<rbrakk> \<Longrightarrow> (f::('a::len) word) < of_nat n"
  by (erule (1)  order_le_less_trans[OF _ of_nat_mono_maybe,rotated]) simp

lemma unat_ucast_less_no_overflow_simp:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat f < n) = ((f::('a::len) word) < of_nat n)"
  using unat_less_helper unat_ucast_less_no_overflow by blast

lemma unat_ucast_no_overflow_le:
  assumes no_overflow: "unat b < (2 :: nat) ^ LENGTH('a)"
  and upward_cast: "LENGTH('a) < LENGTH('b)"
  shows "(ucast (f::'a::len word) < (b :: 'b :: len word)) = (unat f < unat b)"
proof -
  have LR: "ucast f < b \<Longrightarrow> unat f < unat b"
    apply (rule unat_less_helper)
    apply (simp add:ucast_nat_def)
    apply (rule_tac 'b1 = 'b in  ucast_less_ucast[OF order.strict_implies_order, THEN iffD1])
     apply (rule upward_cast)
    apply (simp add: ucast_ucast_mask less_mask_eq word_less_nat_alt
                     unat_power_lower[OF upward_cast] no_overflow)
    done
  have RL: "unat f < unat b \<Longrightarrow> ucast f < b"
  proof-
    assume ineq: "unat f < unat b"
    have "ucast (f::'a::len word) < ((ucast (ucast b ::'a::len word)) :: 'b :: len word)"
      apply (simp add: ucast_less_ucast[OF order.strict_implies_order] upward_cast)
      apply (simp only: flip: ucast_nat_def)
      apply (rule unat_ucast_less_no_overflow[OF no_overflow ineq])
      done
    then show ?thesis
      apply (rule order_less_le_trans)
      apply (simp add:ucast_ucast_mask word_and_le2)
      done
  qed
  then show ?thesis by (simp add:RL LR iffI)
qed

lemmas ucast_up_mono = ucast_less_ucast[THEN iffD2]

lemma minus_one_word:
  "(-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  by simp

lemma le_2p_upper_bits:
  "\<lbrakk> (p::'a::len word) \<le> 2^n - 1; n < LENGTH('a) \<rbrakk> \<Longrightarrow>
  \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> bit p n'"
  by (subst upper_bits_unset_is_l2p; simp)

lemma le2p_bits_unset:
  "p \<le> 2 ^ n - 1 \<Longrightarrow> \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> bit (p::'a::len word) n'"
  using upper_bits_unset_is_l2p [where p=p]
  by (cases "n < LENGTH('a)") auto

lemma complement_nth_w2p:
  shows "n' < LENGTH('a) \<Longrightarrow> bit (NOT (2 ^ n :: 'a::len word)) n' = (n' \<noteq> n)"
  by (fastforce simp: word_ops_nth_size word_size nth_w2p)

lemma word_unat_and_lt:
  "unat x < n \<or> unat y < n \<Longrightarrow> unat (x AND y) < n"
  by (meson le_less_trans word_and_le1 word_and_le2 word_le_nat_alt)

lemma word_unat_mask_lt:
  "m \<le> size w \<Longrightarrow> unat ((w::'a::len word) AND mask m) < 2 ^ m"
  by (rule word_unat_and_lt) (simp add: unat_mask word_size)

lemma word_sless_sint_le:"x <s y \<Longrightarrow> sint x \<le> sint y - 1"
  by (metis word_sless_alt zle_diff1_eq)

lemma upper_trivial:
  fixes x :: "'a::len word"
  shows "x \<noteq> 2 ^ LENGTH('a) - 1 \<Longrightarrow> x < 2 ^ LENGTH('a) - 1"
  by (simp add: less_le)

lemma constraint_expand:
  fixes x :: "'a::len word"
  shows "x \<in> {y. lower \<le> y \<and> y \<le> upper} = (lower \<le> x \<and> x \<le> upper)"
  by (rule mem_Collect_eq)

lemma card_map_elide:
  "card ((of_nat :: nat \<Rightarrow> 'a::len word) ` {0..<n}) = card {0..<n}"
  if "n \<le> CARD('a::len word)"
proof -
  let ?of_nat = "of_nat :: nat \<Rightarrow> 'a word"
  have "inj_on ?of_nat {i. i < CARD('a word)}"
    by (rule inj_onI) (simp add: card_word of_nat_inj)
  moreover have "{0..<n} \<subseteq> {i. i < CARD('a word)}"
    using that by auto
  ultimately have "inj_on ?of_nat {0..<n}"
    by (rule inj_on_subset)
  then show ?thesis
    by (simp add: card_image)
qed

lemma card_map_elide2:
  "n \<le> CARD('a::len word) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> 'a::len word) ` {0..<n}) = n"
  by (subst card_map_elide) clarsimp+

lemma eq_ucast_ucast_eq:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x = ucast y \<Longrightarrow> ucast x = y"
  for x :: "'a::len word" and y :: "'b::len word"
  by transfer simp

lemma le_ucast_ucast_le:
  "x \<le> ucast y \<Longrightarrow> ucast x \<le> y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (smt le_unat_uoi linorder_not_less order_less_imp_le ucast_nat_def unat_arith_simps(1))

lemma less_ucast_ucast_less:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x < ucast y \<Longrightarrow> ucast x < y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (metis ucast_nat_def unat_mono unat_ucast_up_simp word_of_nat_less)

lemma ucast_le_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> (ucast x \<le> (ucast y::'b::len word)) = (x \<le> y)"
  for x :: "'a::len word"
  by (simp add: unat_arith_simps(1) unat_ucast_up_simp)

lemmas ucast_up_mono_le = ucast_le_ucast[THEN iffD2]

lemma ucast_or_distrib:
  fixes x :: "'a::len word"
  fixes y :: "'a::len word"
  shows "(ucast (x OR y) :: ('b::len) word) = ucast x OR ucast y"
  by (fact unsigned_or_eq)

lemma word_exists_nth:
  "(w::'a::len word) \<noteq> 0 \<Longrightarrow> \<exists>i. bit w i"
  by (auto simp add: bit_eq_iff)

lemma max_word_not_0 [simp]:
  "- 1 \<noteq> (0 :: 'a::len word)"
  by simp

lemma unat_max_word_pos[simp]: "0 < unat (- 1 :: 'a::len word)"
  using unat_gt_0 [of \<open>- 1 :: 'a::len word\<close>] by simp


(* Miscellaneous conditional injectivity rules. *)

lemma mult_pow2_inj:
  assumes ws: "m + n \<le> LENGTH('a)"
  assumes le: "x \<le> mask m" "y \<le> mask m"
  assumes eq: "x * 2 ^ n = y * (2 ^ n::'a::len word)"
  shows "x = y"
proof (rule bit_word_eqI)
  fix q
  assume \<open>q < LENGTH('a)\<close>
  from eq have \<open>push_bit n x = push_bit n y\<close>
    by (simp add: push_bit_eq_mult)
  moreover from le have \<open>take_bit m x = x\<close> \<open>take_bit m y = y\<close>
    by (simp_all add: less_eq_mask_iff_take_bit_eq_self)
  ultimately have \<open>push_bit n (take_bit m x) = push_bit n (take_bit m y)\<close>
    by simp_all
  with \<open>q < LENGTH('a)\<close> ws show \<open>bit x q \<longleftrightarrow> bit y q\<close>
    apply (simp add: push_bit_take_bit)
    unfolding bit_eq_iff
    apply (simp add: bit_simps not_le)
    apply (metis (full_types) \<open>take_bit m x = x\<close> \<open>take_bit m y = y\<close> add.commute add_diff_cancel_right' add_less_cancel_right bit_take_bit_iff le_add2 less_le_trans)
    done
qed

lemma word_of_nat_inj:
  assumes bounded: "x < 2 ^ LENGTH('a)" "y < 2 ^ LENGTH('a)"
  assumes of_nats: "of_nat x = (of_nat y :: 'a::len word)"
  shows "x = y"
  by (rule contrapos_pp[OF of_nats]; cases "x < y"; cases "y < x")
     (auto dest: bounded[THEN of_nat_mono_maybe])

lemma word_of_int_bin_cat_eq_iff:
  "(word_of_int (concat_bit LENGTH('b) (uint b) (uint a))::'c::len word) =
  word_of_int (concat_bit LENGTH('b) (uint d) (uint c)) \<longleftrightarrow> b = d \<and> a = c"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len word" and b::"'b::len word"
proof -
  from that show ?thesis
  using that concat_bit_eq_iff [of \<open>LENGTH('b)\<close> \<open>uint b\<close> \<open>uint a\<close> \<open>uint d\<close> \<open>uint c\<close>]
  apply (simp add: word_of_int_eq_iff take_bit_int_eq_self flip: word_eq_iff_unsigned)
  apply (simp add: concat_bit_def take_bit_int_eq_self bintr_uint take_bit_push_bit)
  done
qed

lemma word_cat_inj: "(word_cat a b::'c::len word) = word_cat c d \<longleftrightarrow> a = c \<and> b = d"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len word" and b::"'b::len word"
  using word_of_int_bin_cat_eq_iff [OF that, of b a d c]
  by (simp add: word_cat_eq' ac_simps)

lemma p2_eq_1: "2 ^ n = (1::'a::len word) \<longleftrightarrow> n = 0"
proof -
  have "2 ^ n = (1::'a word) \<Longrightarrow> n = 0"
    by (metis One_nat_def not_less one_less_numeral_iff p2_eq_0 p2_gt_0 power_0 power_0
        power_inject_exp semiring_norm(76) unat_power_lower zero_neq_one)
  then show ?thesis by auto
qed

end

lemmas word_div_less = div_word_less

(* FIXME: move to Word distribution? *)
lemma bin_nth_minus_Bit0[simp]:
  "0 < n \<Longrightarrow> bit (numeral (num.Bit0 w) :: int) n = bit (numeral w :: int) (n - 1)"
  by (cases n; simp)

lemma bin_nth_minus_Bit1[simp]:
  "0 < n \<Longrightarrow> bit (numeral (num.Bit1 w) :: int) n = bit (numeral w :: int) (n - 1)"
  by (cases n; simp)

lemma word_mod_by_0: "k mod (0::'a::len word) = k"
  by (simp add: word_arith_nat_mod)

end
