(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Signed division on word\<close>

theory Signed_Division_Word
  imports "HOL-Library.Signed_Division" "HOL-Library.Word"
begin

text \<open>
  The following specification of division follows ISO C99, which in turn adopted the typical
  behavior of hardware modern in the beginning of the 1990ies.
  The underlying integer division is named ``T-division'' in \cite{leijen01}.
\<close>

instantiation word :: (len) signed_division
begin

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k sdiv signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k smod signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma sdiv_word_def:
  \<open>v sdiv w = word_of_int (sint v sdiv sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma smod_word_def:
  \<open>v smod w = word_of_int (sint v smod sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

instance proof
  fix v w :: \<open>'a word\<close>
  have \<open>sint v sdiv sint w * sint w + sint v smod sint w = sint v\<close>
    by (fact sdiv_mult_smod_eq)
  then have \<open>word_of_int (sint v sdiv sint w * sint w + sint v smod sint w) = (word_of_int (sint v) :: 'a word)\<close>
    by simp
  then show \<open>v sdiv w * w + v smod w = v\<close>
    by (simp add: sdiv_word_def smod_word_def)
qed

end

lemma signed_divide_word_code [code]: \<^marker>\<open>contributor \<open>Andreas Lochbihler\<close>\<close>
  \<open>v sdiv w =
   (let v' = sint v; w' = sint w;
        negative = (v' < 0) \<noteq> (w' < 0);
        result = \<bar>v'\<bar> div \<bar>w'\<bar>
    in word_of_int (if negative then - result else result))\<close>
  for v w :: \<open>'a::len word\<close>
  by (simp add: sdiv_word_def signed_divide_int_def sgn_if)

lemma signed_modulo_word_code [code]: \<^marker>\<open>contributor \<open>Andreas Lochbihler\<close>\<close>
  \<open>v smod w =
   (let v' = sint v; w' = sint w;
        negative = (v' < 0);
        result = \<bar>v'\<bar> mod \<bar>w'\<bar>
    in word_of_int (if negative then - result else result))\<close>
  for v w :: \<open>'a::len word\<close>
  by (simp add: smod_word_def signed_modulo_int_def sgn_if)

lemma sdiv_smod_id:
  \<open>(a sdiv b) * b + (a smod b) = a\<close>
  for a b :: \<open>'a::len word\<close>
  by (fact sdiv_mult_smod_eq)

lemma signed_div_arith:
    "sint ((a::('a::len) word) sdiv b) = signed_take_bit (LENGTH('a) - 1) (sint a sdiv sint b)"
  by (simp add: sdiv_word_def sint_sbintrunc')

lemma signed_mod_arith:
    "sint ((a::('a::len) word) smod b) = signed_take_bit (LENGTH('a) - 1) (sint a smod sint b)"
  by (simp add: sint_sbintrunc' smod_word_def)

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  by (auto simp: sdiv_word_def signed_divide_int_def sgn_if)

lemma smod_word_zero [simp]:
  \<open>w smod 0 = w\<close> for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_signed_take_bit)

lemma word_sdiv_div1 [simp]:
    "(a :: ('a::len) word) sdiv 1 = a"
proof -
  have "sint (- (1::'a word)) = - 1"
    by simp
  then show ?thesis
    by (metis int_sdiv_simps(1) mult_1 mult_minus_left scast_eq scast_id
        sdiv_minus_eq sdiv_word_def signed_1 wi_hom_neg)
qed

lemma smod_word_one [simp]:
  \<open>w smod 1 = 0\<close> for w :: \<open>'a::len word\<close>
  by (simp add: smod_word_def signed_modulo_int_def)

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  by (simp add: sdiv_word_def)

lemma smod_word_minus_one [simp]:
  \<open>w smod - 1 = 0\<close> for w :: \<open>'a::len word\<close>
  by (simp add: smod_word_def signed_modulo_int_def)

lemma one_sdiv_word_eq [simp]:
  \<open>1 sdiv w = of_bool (w = 1 \<or> w = - 1) * w\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>1 < \<bar>sint w\<bar>\<close>)
  case True
  then show ?thesis
    by (auto simp add: sdiv_word_def signed_divide_int_def split: if_splits)
next
  case False
  then have \<open>\<bar>sint w\<bar> \<le> 1\<close>
    by simp
  then have \<open>sint w \<in> {- 1, 0, 1}\<close>
    by auto
  then have \<open>(word_of_int (sint w) :: 'a::len word) \<in> word_of_int ` {- 1, 0, 1}\<close>
    by blast
  then have \<open>w \<in> {- 1, 0, 1}\<close>
    by simp
  then show ?thesis by auto
qed

lemma one_smod_word_eq [simp]:
  \<open>1 smod w = 1 - of_bool (w = 1 \<or> w = - 1)\<close> for w :: \<open>'a::len word\<close>
  using sdiv_smod_id [of 1 w] by auto

lemma minus_one_sdiv_word_eq [simp]:
  \<open>- 1 sdiv w = - (1 sdiv w)\<close> for w :: \<open>'a::len word\<close>
  by (metis (mono_tags, opaque_lifting) minus_sdiv_eq of_int_minus sdiv_word_def signed_1 sint_n1
      word_sdiv_div1 word_sdiv_div_minus1)

lemma minus_one_smod_word_eq [simp]:
  \<open>- 1 smod w = - (1 smod w)\<close> for w :: \<open>'a::len word\<close>
  using sdiv_smod_id [of \<open>- 1\<close> w] by auto

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  by (simp add: minus_sdiv_mult_eq_smod)

lemmas sdiv_word_numeral_numeral [simp] =
  sdiv_word_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_minus_numeral_numeral [simp] =
  sdiv_word_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_numeral_minus_numeral [simp] =
  sdiv_word_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas sdiv_word_minus_numeral_minus_numeral [simp] =
  sdiv_word_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b

lemmas smod_word_numeral_numeral [simp] =
  smod_word_def [of \<open>numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_minus_numeral_numeral [simp] =
  smod_word_def [of \<open>- numeral a\<close> \<open>numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_numeral_minus_numeral [simp] =
  smod_word_def [of \<open>numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b
lemmas smod_word_minus_numeral_minus_numeral [simp] =
  smod_word_def [of \<open>- numeral a\<close> \<open>- numeral b\<close>, simplified sint_sbintrunc sint_sbintrunc_neg]
  for a b

lemmas word_sdiv_0 = word_sdiv_div0

lemma sdiv_word_min:
    "- (2 ^ (size a - 1)) \<le> sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word)"
  by (smt (verit, ccfv_SIG) atLeastAtMost_iff sdiv_int_range sint_ge sint_lt wsst_TYs(3))

lemma sdiv_word_max:
  \<open>sint a sdiv sint b \<le> 2 ^ (size a - Suc 0)\<close>
  for a b :: \<open>'a::len word\<close>
proof (cases \<open>sint a = 0 \<or> sint b = 0 \<or> sgn (sint a) \<noteq> sgn (sint b)\<close>)
  case True then show ?thesis
  proof -
    have "\<And>i j::int. i sdiv j \<le> \<bar>i\<bar>"
      by (meson atLeastAtMost_iff sdiv_int_range)
    then show ?thesis
      by (smt (verit) sint_range_size)
  qed
next
  case False
  then have \<open>\<bar>sint a\<bar> div \<bar>sint b\<bar> \<le> \<bar>sint a\<bar>\<close>
    by (subst nat_le_eq_zle [symmetric]) (simp_all add: div_abs_eq_div_nat)
  also have \<open>\<bar>sint a\<bar> \<le> 2 ^ (size a - Suc 0)\<close>
    using sint_range_size [of a] by auto
  finally show ?thesis
    using False by (simp add: signed_divide_int_def)
qed

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where v="numeral x" for x]
    sdiv_word_def[where v=0] sdiv_word_def[where v=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where w="numeral y" for y]
    word_sdiv_numerals_lhs[where w=0] word_sdiv_numerals_lhs[where w=1]

lemma smod_word_mod_0:
  "x smod (0 :: ('a::len) word) = x"
  by (fact smod_word_zero)

lemma smod_word_0_mod [simp]:
  "0 smod (x :: ('a::len) word) = 0"
  by (clarsimp simp: smod_word_def)

lemma smod_word_max:
  "sint (a::'a word) smod sint (b::'a word) < 2 ^ (LENGTH('a::len) - Suc 0)"
proof (cases \<open>sint b = 0 \<or> LENGTH('a) = 0\<close>)
  case True
  then show ?thesis
    by (force simp: sint_less)
next
  case False
  then show ?thesis
    by (smt (verit) sint_greater_eq sint_less smod_int_compares)
qed

lemma smod_word_min:
  "- (2 ^ (LENGTH('a::len) - Suc 0)) \<le> sint (a::'a word) smod sint (b::'a word)"
  by (smt (verit) sint_greater_eq sint_less smod_int_compares smod_int_mod_0)

lemmas word_smod_numerals_lhs = smod_word_def[where v="numeral x" for x]
    smod_word_def[where v=0] smod_word_def[where v=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where w="numeral y" for y]
    word_smod_numerals_lhs[where w=0] word_smod_numerals_lhs[where w=1]

end
