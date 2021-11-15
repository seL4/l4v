(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Shift operations with infix syntax\<close>

theory Bit_Shifts_Infix_Syntax
  imports "HOL-Library.Word" More_Word
begin

context semiring_bit_operations
begin

definition shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
  where [code_unfold]: \<open>a << n = push_bit n a\<close>

lemma bit_shiftl_iff [bit_simps]:
  \<open>bit (a << m) n \<longleftrightarrow> m \<le> n \<and> possible_bit TYPE('a) n \<and> bit a (n - m)\<close>
  by (simp add: shiftl_def bit_simps)

definition shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  where [code_unfold]: \<open>a >> n = drop_bit n a\<close>

lemma bit_shiftr_eq [bit_simps]:
  \<open>bit (a >> n) = bit a \<circ> (+) n\<close>
  by (simp add: shiftr_def bit_simps)

end

definition sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  where [code_unfold]: \<open>w >>> n = signed_drop_bit n w\<close>

lemma bit_sshiftr_iff [bit_simps]:
  \<open>bit (w >>> m) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else m + n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: sshiftr_def bit_simps)

context
  includes lifting_syntax
begin

lemma shiftl_word_transfer [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (\<lambda>k n. push_bit n k) (<<)\<close>
  apply (unfold shiftl_def)
  apply transfer_prover
  done

lemma shiftr_word_transfer [transfer_rule]:
  \<open>((pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> _) ===> (=) ===> pcr_word)
    (\<lambda>k n. drop_bit n (take_bit LENGTH('a) k))
    (>>)\<close>
proof -
  have \<open>((pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> _) ===> (=) ===> pcr_word)
    (\<lambda>k n. (drop_bit n \<circ> take_bit LENGTH('a)) k)
    (>>)\<close>
    by (unfold shiftr_def) transfer_prover
  then show ?thesis
    by simp
qed

lemma sshiftr_transfer [transfer_rule]:
  \<open>((pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> _) ===> (=) ===> pcr_word)
    (\<lambda>k n. drop_bit n (signed_take_bit (LENGTH('a) - Suc 0) k))
    (>>>)\<close>
proof -
  have \<open>((pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> _) ===> (=) ===> pcr_word)
    (\<lambda>k n. (drop_bit n \<circ> signed_take_bit (LENGTH('a) - Suc 0)) k)
    (>>>)\<close>
    by (unfold sshiftr_def) transfer_prover
  then show ?thesis
    by simp
qed

end

context semiring_bit_operations
begin

lemma shiftl_0 [simp]:
  \<open>0 << n = 0\<close>
  by (simp add: shiftl_def)

lemma shiftl_of_0 [simp]:
  \<open>a << 0 = a\<close>
  by (simp add: shiftl_def)

lemma shiftl_of_Suc [simp]:
  \<open>a << Suc n = (a * 2) << n\<close>
  by (simp add: shiftl_def)

lemma shiftl_1 [simp]:
  \<open>1 << n = 2 ^ n\<close>
  by (simp add: shiftl_def)

lemma shiftl_numeral_Suc [simp]:
  \<open>numeral m << Suc n = push_bit (Suc n) (numeral m)\<close>
  by (fact shiftl_def)

lemma shiftl_numeral_numeral [simp]:
  \<open>numeral m << numeral n = push_bit (numeral n) (numeral m)\<close>
  by (fact shiftl_def)

lemma shiftr_0 [simp]:
  \<open>0 >> n = 0\<close>
  by (simp add: shiftr_def)

lemma shiftr_of_0 [simp]:
  \<open>a >> 0 = a\<close>
  by (simp add: shiftr_def)

lemma shiftr_1 [simp]:
  \<open>1 >> n = of_bool (n = 0)\<close>
  by (simp add: shiftr_def)

lemma shiftr_numeral_Suc [simp]:
  \<open>numeral m >> Suc n = drop_bit (Suc n) (numeral m)\<close>
  by (fact shiftr_def)

lemma shiftr_numeral_numeral [simp]:
  \<open>numeral m >> numeral n = drop_bit (numeral n) (numeral m)\<close>
  by (fact shiftr_def)

lemma shiftl_eq_mult:
  \<open>x << n = x * 2 ^ n\<close>
  unfolding shiftl_def by (fact push_bit_eq_mult)

lemma shiftr_eq_div:
  \<open>x >> n = x div 2 ^ n\<close>
  unfolding shiftr_def by (fact drop_bit_eq_div)

end

context ring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma shiftl_minus_1_numeral [simp]:
  \<open>- 1 << numeral n = NOT (mask (numeral n))\<close>
  by (simp add: shiftl_def)

end

end

lemma shiftl_Suc_0 [simp]:
  \<open>Suc 0 << n = 2 ^ n\<close>
  by (simp add: shiftl_def)

lemma shiftr_Suc_0 [simp]:
  \<open>Suc 0 >> n = of_bool (n = 0)\<close>
  by (simp add: shiftr_def)

lemma sshiftr_numeral_Suc [simp]:
  \<open>numeral m >>> Suc n = signed_drop_bit (Suc n) (numeral m)\<close>
  by (fact sshiftr_def)

lemma sshiftr_numeral_numeral [simp]:
  \<open>numeral m >>> numeral n = signed_drop_bit (numeral n) (numeral m)\<close>
  by (fact sshiftr_def)

context ring_bit_operations
begin

lemma shiftl_minus_numeral_Suc [simp]:
  \<open>- numeral m << Suc n = push_bit (Suc n) (- numeral m)\<close>
  by (fact shiftl_def)

lemma shiftl_minus_numeral_numeral [simp]:
  \<open>- numeral m << numeral n = push_bit (numeral n) (- numeral m)\<close>
  by (fact shiftl_def)

lemma shiftr_minus_numeral_Suc [simp]:
  \<open>- numeral m >> Suc n = drop_bit (Suc n) (- numeral m)\<close>
  by (fact shiftr_def)

lemma shiftr_minus_numeral_numeral [simp]:
  \<open>- numeral m >> numeral n = drop_bit (numeral n) (- numeral m)\<close>
  by (fact shiftr_def)

end

lemma sshiftr_0 [simp]:
  \<open>0 >>> n = 0\<close>
  by (simp add: sshiftr_def)

lemma sshiftr_of_0 [simp]:
  \<open>w >>> 0 = w\<close>
  by (simp add: sshiftr_def)

lemma sshiftr_1 [simp]:
  \<open>(1 :: 'a::len word) >>> n = of_bool (LENGTH('a) = 1 \<or> n = 0)\<close>
  by (simp add: sshiftr_def)

lemma sshiftr_minus_numeral_Suc [simp]:
  \<open>- numeral m >>> Suc n = signed_drop_bit (Suc n) (- numeral m)\<close>
  by (fact sshiftr_def)

lemma sshiftr_minus_numeral_numeral [simp]:
  \<open>- numeral m >>> numeral n = signed_drop_bit (numeral n) (- numeral m)\<close>
  by (fact sshiftr_def)

end
