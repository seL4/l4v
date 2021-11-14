(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section \<open>64 bit standard platform-specific word size and alignment.\<close>

theory Machine_Word_64_Basics
imports "HOL-Library.Word" Word_64
begin

type_synonym machine_word_len = 64

definition word_bits :: nat
where
  \<open>word_bits = LENGTH(machine_word_len)\<close>

lemma word_bits_conv [code]:
  \<open>word_bits = 64\<close>
  by (simp add: word_bits_def)

text \<open>The following two are numerals so they can be used as nats and words.\<close>

definition word_size_bits :: \<open>'a :: numeral\<close>
where
  \<open>word_size_bits = 3\<close>

definition word_size :: \<open>'a :: numeral\<close>
where
  \<open>word_size = 8\<close>

lemma n_less_word_bits:
  "(n < word_bits) = (n < 64)"
  by (simp add: word_bits_def word_size_def)

lemmas upper_bits_unset_is_l2p_64 = upper_bits_unset_is_l2p [where 'a=64, folded word_bits_def]

lemmas le_2p_upper_bits_64 = le_2p_upper_bits [where 'a=64, folded word_bits_def]
lemmas le2p_bits_unset_64 = le2p_bits_unset[where 'a=64, folded word_bits_def]

lemmas unat_power_lower64 [simp] = unat_power_lower64'[folded word_bits_def]

lemmas word64_less_sub_le[simp] = word64_less_sub_le' [folded word_bits_def]

lemmas word64_power_less_1[simp] = word64_power_less_1'[folded word_bits_def]

lemma of_nat64_0:
  "\<lbrakk>of_nat n = (0::word64); n < 2 ^ word_bits\<rbrakk> \<Longrightarrow> n = 0"
  by (erule of_nat_0, simp add: word_bits_def)

lemmas unat_of_nat64 = unat_of_nat64'[folded word_bits_def]

lemmas word_power_nonzero_64 = word_power_nonzero [where 'a=64, folded word_bits_def]

lemmas div_power_helper_64 = div_power_helper [where 'a=64, folded word_bits_def]

lemmas of_nat_less_pow_64 = of_nat_power [where 'a=64, folded word_bits_def]

lemmas unat_mask_word64 = unat_mask_word64'[folded word_bits_def]

end
