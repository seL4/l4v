(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Word_Lemmas_64_Internal
imports Word_Lib_Sumo Word_64 Machine_Word_64
begin

(* This is why Word_Lib_Sumo doesn't really work: *)
lemmas word_and_max_simps = word_and_max_simps word64_and_max_simp

lemmas unat_add_simple = iffD1[OF unat_add_lem[where 'a = 64, folded word_bits_def]]

lemma unat_length_4_helper:
  "\<lbrakk>unat (l::machine_word) = length args; \<not> l < 4\<rbrakk> \<Longrightarrow> \<exists>x xa xb xc xs. args = x#xa#xb#xc#xs"
  apply (case_tac args; clarsimp simp: unat_eq_0)
  by (rename_tac list, case_tac list, clarsimp, unat_arith)+

lemma ucast_drop_big_mask:
  "UCAST(64 \<rightarrow> 16) (x && 0xFFFF) = UCAST(64 \<rightarrow> 16) x"
  by word_bitwise

lemma first_port_last_port_compare:
  "UCAST(16 \<rightarrow> 32 signed) (UCAST(64 \<rightarrow> 16) (xa && 0xFFFF))
        <s UCAST(16 \<rightarrow> 32 signed) (UCAST(64 \<rightarrow> 16) (x && 0xFFFF))
       = (UCAST(64 \<rightarrow> 16) xa < UCAST(64 \<rightarrow> 16) x)"
  apply (clarsimp simp: word_sless_alt ucast_drop_big_mask)
  apply (subst sint_ucast_eq_uint, clarsimp simp: is_down)+
  by (simp add: word_less_alt)

lemma machine_word_and_3F_less_40:
  "(w :: machine_word) && 0x3F < 0x40"
  by (rule word_and_less', simp)

lemmas unat64_eq_of_nat = unat_eq_of_nat[where 'a=64, folded word_bits_def]

lemma unat_mask_3_less_8:
  "unat (p && mask 3 :: word64) < 8"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

lemma scast_specific_plus64:
  "scast (of_nat (word_ctz x) + 0x20 :: 64 signed word) = of_nat (word_ctz x) + (0x20 :: machine_word)"
  by (metis of_nat_add of_nat_numeral scast_of_nat)

lemma scast_specific_plus64_signed:
  "scast (of_nat (word_ctz x) + 0x20 :: machine_word) = of_nat (word_ctz x) + (0x20 :: 64 signed word)"
  by (metis scast_scast_id(2) scast_specific_plus64)

lemmas mask_64_id[simp] = mask_len_id[where 'a=64, folded word_bits_def]
                          mask_len_id[where 'a=64, simplified]

lemma neq_0_unat: "x \<noteq> 0 \<Longrightarrow> 0 < unat x" for x::machine_word
  by (simp add: unat_gt_0)

end