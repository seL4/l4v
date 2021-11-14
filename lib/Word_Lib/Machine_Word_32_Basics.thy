(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section \<open>32 bit standard platform-specific word size and alignment.\<close>

theory Machine_Word_32_Basics
imports "HOL-Library.Word" Word_32
begin

type_synonym machine_word_len = 32

definition word_bits :: nat
where
  \<open>word_bits = LENGTH(machine_word_len)\<close>

lemma word_bits_conv [code]:
  \<open>word_bits = 32\<close>
  by (simp add: word_bits_def)

text \<open>The following two are numerals so they can be used as nats and words.\<close>

definition word_size_bits :: \<open>'a :: numeral\<close>
where
  \<open>word_size_bits = 2\<close>

definition word_size :: \<open>'a :: numeral\<close>
where
  \<open>word_size = 4\<close>

lemma n_less_word_bits:
  "(n < word_bits) = (n < 32)"
  by (simp add: word_bits_def word_size_def)

lemmas upper_bits_unset_is_l2p_32 = upper_bits_unset_is_l2p [where 'a=32, folded word_bits_def]

lemmas le_2p_upper_bits_32 = le_2p_upper_bits [where 'a=32, folded word_bits_def]
lemmas le2p_bits_unset_32 = le2p_bits_unset[where 'a=32, folded word_bits_def]

lemmas unat_power_lower32 [simp] = unat_power_lower32'[folded word_bits_def]

lemmas word32_less_sub_le[simp] = word32_less_sub_le' [folded word_bits_def]

lemmas word32_power_less_1[simp] = word32_power_less_1'[folded word_bits_def]

lemma of_nat32_0:
  "\<lbrakk>of_nat n = (0::word32); n < 2 ^ word_bits\<rbrakk> \<Longrightarrow> n = 0"
  by (erule of_nat_0, simp add: word_bits_def)

lemmas unat_of_nat32 = unat_of_nat32'[folded word_bits_def]

lemmas word_power_nonzero_32 = word_power_nonzero [where 'a=32, folded word_bits_def]

lemmas div_power_helper_32 = div_power_helper [where 'a=32, folded word_bits_def]

lemmas of_nat_less_pow_32 = of_nat_power [where 'a=32, folded word_bits_def]

lemmas unat_mask_word32 = unat_mask_word32'[folded word_bits_def]

end
