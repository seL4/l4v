(*
 * Copyright 2018, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Word_Lemmas_32_Internal
imports Word_Lemmas_32
begin

lemmas sint_eq_uint_32 = sint_eq_uint_2pl[where 'a=32, simplified]

lemmas sle_positive_32 = sle_le_2pl[where 'a=32, simplified]

lemmas sless_positive_32 = sless_less_2pl[where 'a=32, simplified]

lemma zero_le_sint_32:
  "\<lbrakk> 0 \<le> (a :: word32); a < 0x80000000 \<rbrakk>
   \<Longrightarrow> 0 \<le> sint a"
  by (clarsimp simp: sint_eq_uint_32 unat_less_helper)

lemmas unat_add_simple = iffD1[OF unat_add_lem[where 'a = 32, folded word_bits_def]]

lemma upto_enum_inc_1:
  "a < 2 ^ word_bits - 1
   \<Longrightarrow> [(0:: 'a :: len word) .e. 1 + a] = [0.e.a] @ [(1+a)]"
  using upper_trivial upto_enum_inc_1_len by force

lemmas upt_enum_offset_trivial =
  upt_enum_offset_trivial[where 'a=32, folded word_bits_def]

lemmas unat32_eq_of_nat = unat_eq_of_nat[where 'a=32, folded word_bits_def]

declare mask_32_max_word[simp]

lemma le_32_mask_eq:
  "(bits :: word32) \<le> 32 \<Longrightarrow> bits && mask 6 = bits"
  by (fastforce elim: le_less_trans intro: less_mask_eq)

lemmas scast_1_32[simp] = scast_1[where 'a=32]

lemmas mask_32_id[simp] = mask_len_id[where 'a=32, folded word_bits_def]

lemmas t2p_shiftr_32 = t2p_shiftr[where 'a=32, folded word_bits_def]

lemma mask_eq1_nochoice:
  "(x :: word32) && 1 = x
   \<Longrightarrow> x = 0 \<or> x = 1"
  using mask_eq1_nochoice len32 by force

lemmas const_le_unat_word_32 = const_le_unat[where 'a=32, folded word_bits_def]

lemmas createNewCaps_guard_helper =
  createNewCaps_guard[where 'a=32, folded word_bits_def]

lemma word_log2_max_word32[simp]:
  "word_log2 (w :: 32 word) < 32"
  using word_log2_max[where w=w]
  by (simp add: word_size)

(* FIXME: specialize using pow_sub_less_word *)
lemma mapping_two_power_16_64_inequality:
  assumes sz: "sz \<le> 4" and len: "unat (len :: word32) = 2 ^ sz"
  shows "unat (len * 8 - 1) \<le> 127"
  using pow_sub_less[where 'a=32 and b=3, simplified]
proof -
  have len2: "len = 2 ^ sz"
    apply (rule word_unat.Rep_eqD, simp only: len)
    using sz
    apply simp
    done

  show ?thesis using two_power_increasing_less_1[where 'a=32 and n="sz + 3" and m=7]
    by (simp add: word_le_nat_alt sz power_add len2 field_simps)
qed

lemmas pre_helper2_32 = pre_helper2[where 'a=32, folded word_bits_def]

lemmas of_nat_shift_distinct_helper_machine =
  of_nat_shift_distinct_helper[where 'a=32, folded word_bits_def]

lemmas ptr_add_distinct_helper_32 =
  ptr_add_distinct_helper[where 'a=32, folded word_bits_def]

lemmas mask_out_eq_0_32 = mask_out_eq_0[where 'a=32, folded word_bits_def]

lemmas neg_mask_mask_unat_32 = neg_mask_mask_unat[where 'a=32, folded word_bits_def]

lemmas unat_less_iff_32 = unat_less_iff[where 'a=32, folded word_bits_def]

lemmas is_aligned_no_overflow3_32 = is_aligned_no_overflow3[where 'a=32, folded word_bits_def]

lemmas unat_ucast_16_32 = unat_signed_ucast_less_ucast[where 'a=16 and 'b=32, simplified]

(* FIXME: generalize? *)
lemma scast_mask_8:
  "scast (mask 8 :: sword32) = (mask 8 :: word32)"
  by (clarsimp simp: mask_def)

lemmas ucast_le_8_32_equiv = ucast_le_up_down_iff[where 'a=8 and 'b=32, simplified]

lemma signed_unat_minus_one_32:
  "unat (-1 :: 32 signed word) = 4294967295"
  by (simp del: word_pow_0 diff_0 add: unat_sub_if' minus_one_word)

lemmas two_bits_cases_32 = two_bits_cases[where 'a=32, simplified]

lemmas word_ctz_not_minus_1_32 = word_ctz_not_minus_1[where 'a=32, simplified]

lemmas sint_ctz_32 = sint_ctz[where 'a=32, simplified]

(* FIXME: inline these? *)
lemmas scast_specific_plus32 =
  scast_of_nat_signed_to_unsigned_add[where 'a=32 and x="word_ctz x" and y="0x20" for x,
                                      simplified]
lemmas scast_specific_plus32_signed =
  scast_of_nat_unsigned_to_signed_add[where 'a=32 and x="word_ctz x" and y="0x20" for x,
                                      simplified]

end