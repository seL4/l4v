(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "64-Bit Machine Word Setup"

theory Machine_Word_64
imports Machine_Word_64_Basics More_Word Bit_Shifts_Infix_Syntax Rsplit
begin

context
  includes bit_operations_syntax
begin

type_synonym machine_word = \<open>machine_word_len word\<close>

lemma word_bits_len_of:
  \<open>LENGTH(machine_word_len) = word_bits\<close>
  by (simp add: word_bits_conv)

lemma word_bits_size:
  "size (w :: machine_word) = word_bits"
  by (simp add: word_bits_def word_size)

lemma word_bits_word_size_conv:
  \<open>word_bits = word_size * 8\<close>
  by (simp add: word_bits_def word_size_def)

lemma word_size_word_size_bits:
  \<open>word_size = (2 :: 'a :: semiring_1) ^ word_size_bits\<close>
  by (simp add: word_size_def word_size_bits_def)

lemma lt_word_bits_lt_pow:
  "sz < word_bits \<Longrightarrow> sz < 2 ^ word_bits"
  by (simp add: word_bits_conv)

lemma if_then_1_else_0:
  "((if P then 1 else 0) = (0 :: machine_word)) = (\<not> P)"
  by simp

lemma if_then_0_else_1:
  "((if P then 0 else 1) = (0 :: machine_word)) = (P)"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0

lemma bool_mask [simp]:
  \<open>0 < x AND 1 \<longleftrightarrow> x AND 1 = 1\<close> for x :: machine_word
  by (rule bool_mask') auto

lemma in_16_range:
  "0 \<in> S \<Longrightarrow> r \<in> (\<lambda>x. r + x * (16 :: machine_word)) ` S"
  "n - 1 \<in> S \<Longrightarrow> (r + (16 * n - 16)) \<in> (\<lambda>x :: machine_word. r + x * 16) ` S"
  by (clarsimp simp: image_def elim!: bexI[rotated])+

lemma le_step_down_word_3:
  fixes x :: machine_word
  shows "\<lbrakk>x \<le> y; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (fact le_step_down_word_2)

lemma shiftr_1:
  "(x::machine_word) >> 1 = 0 \<Longrightarrow> x < 2"
  apply transfer
  apply (simp add: take_bit_drop_bit)
  apply (simp add: drop_bit_Suc)
  done

lemma Suc_unat_mask_div:
  "Suc (unat (mask sz div word_size :: machine_word)) = 2 ^ (min sz word_bits - word_size_bits)"
  by (simp add: word_size_word_size_bits unat_drop_bit_eq unat_mask_eq drop_bit_mask_eq Suc_mask_eq_exp
    flip: drop_bit_eq_div word_bits_conv)

lemma ucast_not_helper:
  fixes a::"8 word"
  assumes a: "a \<noteq> 0xFF"
  shows "ucast a \<noteq> (0xFF::machine_word)"
proof
  assume "ucast a = (0xFF::machine_word)"
  also
  have "(0xFF::machine_word) = ucast (0xFF::8 word)" by simp
  finally
  show False using a
    apply -
    apply (drule up_ucast_inj, simp)
    apply simp
    done
qed

lemma unat_less_2p_word_bits:
  "unat (x :: machine_word) < 2 ^ word_bits"
  apply (simp only: word_bits_def)
  apply (rule unat_lt2p)
  done

lemma unat_less_word_bits:
  fixes y :: machine_word
  shows "x < unat y \<Longrightarrow> x < 2 ^ word_bits"
  unfolding word_bits_def
  by (rule order_less_trans [OF _ unat_lt2p])

lemma unat_mask_2_less_4:
  "unat (p AND mask 2 :: machine_word) < 4"
  by (rule unat_less_helper) (simp only: take_bit_eq_mod word_mod_less_divisor flip: take_bit_eq_mask, simp add: word_mod_less_divisor)

lemma unat_mult_simple:
  \<open>unat (x * y) = unat x * unat y\<close>
    if \<open>unat x * unat y < 2 ^ LENGTH(machine_word_len)\<close>
    for x y :: machine_word
  using that by (simp flip: unat_mult_lem)

lemma upto_2_helper:
  "{0..<2 :: machine_word} = {0, 1}"
  by (safe; simp) unat_arith

lemma word_ge_min:
  \<open>- (2 ^ (word_bits - 1)) \<le> sint x\<close> for x :: machine_word
  using sint_ge [of x] by (simp add: word_bits_def)

lemma word_rsplit_0:
  "word_rsplit (0 :: machine_word) = replicate (word_bits div 8) (0 :: 8 word)"
  by (simp add: word_rsplit_def bin_rsplit_def word_bits_def word_size_def Cons_replicate_eq)

lemma x_less_2_0_1:
  fixes x :: machine_word
  shows "x < 2 \<Longrightarrow> x = 0 \<or> x = 1"
  by (rule x_less_2_0_1') auto

end

end
