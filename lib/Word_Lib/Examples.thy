(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Examples
  imports
    Bit_Shifts_Infix_Syntax Next_and_Prev Signed_Division_Word Bitwise
begin

context
  includes bit_operations_syntax
begin

section \<open>\<^typ>\<open>nat\<close>\<close>

lemma
  \<open>bit (1705 :: nat) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>bit (1705 :: nat) 3\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: nat) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: nat) 3\<close>
  by simp

lemma
  \<open>(1705 :: nat) AND 42 = 40\<close>
  by simp

lemma
  \<open>(1705 :: nat) AND Suc 0 = 1\<close>
  by simp

lemma
  \<open>(1705 :: nat) OR 42 = 1707\<close>
  by simp

lemma
  \<open>(1705 :: nat) OR Suc 0 = 1705\<close>
  by simp

lemma
  \<open>(1705 :: nat) XOR 42 = 1667\<close>
  by simp

lemma
  \<open>(1705 :: nat) XOR 1 = 1704\<close>
  by simp

lemma
  \<open>push_bit 3 (1705 :: nat) = 13640\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 13640\<close>
  by simp

lemma
  \<open>push_bit 3 (Suc 0) = 8\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (Suc 0) = 8\<close>
  by simp

lemma
  \<open>(1705 :: nat) << 3 = 13640\<close>
  by simp

lemma
  \<open>(1705 :: nat) << Suc (Suc (Suc 0)) = 13640\<close>
  by simp

lemma
  \<open>Suc 0 << 3 = 8\<close>
  by simp

lemma
  \<open>Suc 0 << Suc (Suc (Suc 0)) = 8\<close>
  by simp

lemma
  \<open>drop_bit 3 (1705 :: nat) = 213\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 213\<close>
  by simp

lemma
  \<open>drop_bit 3 (Suc 0) = 0\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (Suc 0) = 0\<close>
  by simp

lemma
  \<open>(1705 :: nat) >> 3 = 213\<close>
  by simp

lemma
  \<open>(1705 :: nat) >> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma
  \<open>Suc 0 >> 3 = 0\<close>
  by simp

lemma
  \<open>Suc 0 >> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma
  \<open>take_bit 3 (1705 :: nat) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma
  \<open>take_bit 3 (Suc 0) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (Suc 0) = 1\<close>
  by simp


section \<open>\<^typ>\<open>int\<close>\<close>

lemma
  \<open>bit (1705 :: int) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>bit (1705 :: int) 3\<close>
  by simp

lemma
  \<open>\<not> bit (- 1705 :: int) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>\<not> bit (- 1705 :: int) 3\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: int) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: int) 3\<close>
  by simp

lemma
  \<open>(NOT 1705 :: int) = - 1706\<close>
  by simp

lemma
  \<open>(NOT (- 42 :: int)) = 41\<close>
  by simp

lemma
  \<open>(NOT 1 :: int) = - 2\<close>
  by simp

lemma
  \<open>(1705 :: int) AND 42 = 40\<close>
  by simp

lemma
  \<open>(1705 :: int) AND - 42 = 1664\<close>
  by simp

lemma
  \<open>(1705 :: int) AND 1 = 1\<close>
  by simp

lemma
  \<open>- (1705 :: int) AND 42 = 2\<close>
  by simp

lemma
  \<open>- (1705 :: int) AND - 42 = - 1706\<close>
  by simp

lemma
  \<open>- (1705 :: int) AND 1 = 1\<close>
  by simp

lemma
  \<open>(1705 :: int) OR 42 = 1707\<close>
  by simp

lemma
  \<open>(1705 :: int) OR - 42 = - 1\<close>
  by simp

lemma
  \<open>(1705 :: int) OR 1 = 1705\<close>
  by simp

lemma
  \<open>- (1705 :: int) OR 42 = - 1665\<close>
  by simp

lemma
  \<open>- (1705 :: int) OR - 42 = - 41\<close>
  by simp

lemma
  \<open>- (1705 :: int) OR 1 = - 1705\<close>
  by simp

lemma
  \<open>(1705 :: int) XOR 42 = 1667\<close>
  by simp

lemma
  \<open>(1705 :: int) XOR - 42 = - 1665\<close>
  by simp

lemma
  \<open>(1705 :: int) XOR 1 = 1704\<close>
  by simp

lemma
  \<open>- (1705 :: int) XOR 42 = - 1667\<close>
  by simp

lemma
  \<open>- (1705 :: int) XOR - 42 = 1665\<close>
  by simp

lemma
  \<open>- (1705 :: int) XOR 1 = - 1706\<close>
  by simp

lemma
  \<open>push_bit 3 (1705 :: int) = 13640\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: int) = 13640\<close>
  by simp

lemma
  \<open>push_bit 3 (- 1705 :: int) = - 13640\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 13640\<close>
  by simp

lemma
  \<open>push_bit 3 (1 :: int) = 8\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (1 :: int) = 8\<close>
  by simp

lemma
  \<open>push_bit 3 (- 1 :: int) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: int) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>(1705 :: int) << 3  = 13640\<close>
  by simp

lemma
  \<open>(1705 :: int) << Suc (Suc (Suc 0)) = 13640\<close>
  by simp

lemma
  \<open>(- 1705 :: int) << 3 = - 13640\<close>
  by simp

lemma
  \<open>(- 1705 :: int) << Suc (Suc (Suc 0)) = - 13640\<close>
  by simp

lemma
  \<open>(1 :: int) << 3 = 8\<close>
  by simp

lemma
  \<open>(1 :: int) << Suc (Suc (Suc 0)) = 8\<close>
  by simp

lemma
  \<open>(- 1 :: int) << 3 = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>(- 1 :: int) << Suc (Suc (Suc 0)) = - 8\<close>
  by simp

lemma
  \<open>drop_bit 3 (1705 :: int) = 213\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: int) = 213\<close>
  by simp

lemma
  \<open>drop_bit 3 (- 1705 :: int) = - 214\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 214\<close>
  by simp

lemma
  \<open>drop_bit 3 (1 :: int) = 0\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: int) = 0\<close>
  by simp

lemma
  \<open>(1705 :: int) >> 3 = 213\<close>
  by simp

lemma
  \<open>(1705 :: int) >> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma
  \<open>(- 1705 :: int) >> 3 = - 214\<close>
  by simp

lemma
  \<open>(- 1705 :: int) >> Suc (Suc (Suc 0)) = - 214\<close>
  by simp

lemma
  \<open>(1 :: int) >> 3 = 0\<close>
  by simp

lemma
  \<open>(1 :: int) >> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma
  \<open>take_bit 3 (1705 :: int) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: int) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma
  \<open>take_bit 3 (- 1705 :: int) = 7\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close>
  by (simp flip: add_2_eq_Suc)

lemma
  \<open>take_bit 3 (1 :: int) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close>
  by simp

lemma
  \<open>take_bit 3 (- 1 :: int) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: int) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>signed_take_bit 3 (1705 :: int) = - 7\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: int) = - 7\<close>
  by simp

lemma
  \<open>signed_take_bit 3 (- 1705 :: int) = 7\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close>
  by simp

lemma
  \<open>signed_take_bit 3 (1 :: int) = 1\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close>
  by simp


section \<open>\<^typ>\<open>'a word\<close>\<close>

lemma
  \<open>(1705 :: 8 word) = 169\<close>
  by simp

lemma
  \<open>(- 1705 :: 8 word) = 87\<close>
  by simp

lemma
  \<open>(257 :: 8 word) = 1\<close>
  by simp

lemma
  \<open>(42 :: 8 word) \<le> 1705\<close>
  by simp

lemma
  \<open>(- 42 :: 8 word) \<le> 230\<close>
  by simp

lemma
  \<open>(42 :: 8 word) \<le> - 1705\<close>
  by simp

lemma
  \<open>- (42 :: 8 word) \<le> 235\<close>
  by simp

lemma
  \<open>(1 :: 8 word) \<le> 1705\<close>
  by simp

lemma
  \<open>(- 1 :: 8 word) \<le> 65535\<close>
  by simp

lemma
  \<open>(42 :: 8 word) < 1705\<close>
  by simp

lemma
  \<open>(- 42 :: 8 word) < 230\<close>
  by simp

lemma
  \<open>(42 :: 8 word) < - 1705\<close>
  by simp

lemma
  \<open>- (42 :: 8 word) < 230\<close>
  by simp

lemma
  \<open>(1 :: 8 word) < 1705\<close>
  by simp

lemma
  \<open>(1705 :: 8 word) < - 1\<close>
  by simp

lemma
  \<open>(42 :: 8 word) \<le>s 1333\<close>
  by simp

lemma
  \<open>(- 42 :: 8 word) \<le>s 230\<close>
  by simp

lemma
  \<open>(42 :: 8 word) \<le>s - 1705\<close>
  by simp

lemma
  \<open>- (42 :: 8 word) \<le>s - 1705\<close>
  by simp

lemma
  \<open>(1 :: 8 word) \<le>s 42\<close>
  by simp

lemma
  \<open>(42 :: 8 word) <s 1333\<close>
  by simp

lemma
  \<open>(- 42 :: 8 word) <s 230\<close>
  by simp

lemma
  \<open>(42 :: 8 word) <s - 1705\<close>
  by simp

lemma
  \<open>- (42 :: 8 word) <s - 1705\<close>
  by simp

lemma
  \<open>(1 :: 8 word) <s 42\<close>
  by simp

lemma
  \<open>bit (1705 :: 16 word) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>bit (1705 :: 16 word) 3\<close>
  by simp

lemma
  \<open>\<not> bit (- 1705 :: 16 word) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>\<not> bit (- 1705 :: 16 word) 3\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: 'a::len word) (Suc (Suc (Suc 0)))\<close>
  by simp

lemma
  \<open>\<not> bit (1 :: 'a::len word) 3\<close>
  by simp

lemma
  \<open>(NOT 1705 :: 'a::len word) = - 1706\<close>
  by simp

lemma
  \<open>(NOT (- 42 :: 'a::len word)) = 41\<close>
  by simp

lemma
  \<open>(NOT 1 :: 'a::len word) = - 2\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) AND 42 = 40\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) AND - 42 = 1664\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) AND 1 = 1\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) AND 42 = 2\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) AND - 42 = - 1706\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) AND 1 = 1\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) OR 42 = 1707\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) OR - 42 = - 1\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) OR 1 = 1705\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) OR 42 = - 1665\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) OR - 42 = - 41\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) OR 1 = - 1705\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) XOR 42 = 1667\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) XOR - 42 = - 1665\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) XOR 1 = 1704\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) XOR 42 = - 1667\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) XOR - 42 = 1665\<close>
  by simp

lemma
  \<open>- (1705 :: 'a::len word) XOR 1 = - 1706\<close>
  by simp

lemma
  \<open>push_bit 3 (1705 :: 'a::len word) = 13640\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: 'a::len word) = 13640\<close>
  by simp

lemma
  \<open>push_bit 3 (- 1705 :: 'a::len word) = - 13640\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: 'a::len word) = - 13640\<close>
  by simp

lemma
  \<open>push_bit 3 (1 :: 'a::len word) = 8\<close>
  by simp

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (1 :: 'a::len word) = 8\<close>
  by simp

lemma
  \<open>push_bit 3 (- 1 :: 'a::len word) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: 'a::len word) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>(1705 :: 'a::len word) << 3 = 13640\<close>
  by simp

lemma
  \<open>(1705 :: 'a::len word) << Suc (Suc (Suc 0)) = 13640\<close>
  by simp

lemma
  \<open>(- 1705 :: 'a::len word) << 3 = - 13640\<close>
  by simp

lemma
  \<open>(- 1705 :: 'a::len word) << Suc (Suc (Suc 0)) = - 13640\<close>
  by simp

lemma
  \<open>(1 :: 'a::len word) << 3 = 8\<close>
  by simp

lemma
  \<open>(1 :: 'a::len word) << Suc (Suc (Suc 0)) = 8\<close>
  by simp

lemma
  \<open>(- 1 :: 'a::len word) << 3 = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>(- 1 :: 'a::len word) << Suc (Suc (Suc 0)) = - 8\<close>
  by simp

lemma
  \<open>drop_bit 3 (1705 :: 16 word) = 213\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close>
  by simp

lemma
  \<open>drop_bit 3 (- 1705 :: 16 word) = 7978\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7978\<close>
  by simp

lemma
  \<open>drop_bit 3 (1 :: 16 word) = 0\<close>
  by simp

lemma
  \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) >> 3 = 213\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) >> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) >> 3 = 7978\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) >> Suc (Suc (Suc 0)) = 7978\<close>
  by simp

lemma
  \<open>(1 :: 16 word) >> 3 = 0\<close>
  by simp

lemma
  \<open>(1 :: 16 word) >> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma
  \<open>signed_drop_bit 3 (1705 :: 16 word) = 213\<close>
  by simp

lemma
  \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close>
  by simp

lemma
  \<open>signed_drop_bit 3 (- 1705 :: 16 word) = - 214\<close>
  by simp

lemma
  \<open>signed_drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = - 214\<close>
  by simp

lemma
  \<open>signed_drop_bit 3 (1 :: 16 word) = 0\<close>
  by simp

lemma
  \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) >>> 3 = 213\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) >>> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) >>> 3 = - 214\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) >>> Suc (Suc (Suc 0)) = - 214\<close>
  by simp

lemma
  \<open>(1 :: 16 word) >>> 3 = 0\<close>
  by simp

lemma
  \<open>(1 :: 16 word) >>> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma
  \<open>take_bit 3 (1705 :: 16 word) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma
  \<open>take_bit 3 (- 1705 :: 16 word) = 7\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close>
  by (simp flip: add_2_eq_Suc)

lemma
  \<open>take_bit 3 (1 :: 16 word) = 1\<close>
  by simp

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close>
  by simp

lemma
  \<open>take_bit 3 (- 1 :: 16 word) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: 16 word) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma
  \<open>signed_take_bit 3 (1705 :: 16 word) = - 7\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = - 7\<close>
  by simp

lemma
  \<open>signed_take_bit 3 (- 1705 :: 16 word) = 7\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close>
  by simp

lemma
  \<open>signed_take_bit 3 (1 :: 16 word) = 1\<close>
  by simp

lemma
  \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) div 42 = 40\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) div 42 = 1519\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) div - 42 = 0\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) div - 42 = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) div 1 = 1705\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) div - 1 = 0\<close>
  by simp

lemma
  \<open>(1 :: 16 word) div 42 = 0\<close>
  by simp

lemma
  \<open>(- 1 :: 16 word) div 42 = 1560\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) mod 42 = 25\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) mod 42 = 33\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) mod - 42 = 1705\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) mod - 42 = 63831\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) mod 1 = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) mod - 1 = 1705\<close>
  by simp

lemma
  \<open>(1 :: 16 word) mod 42 = 1\<close>
  by simp

lemma
  \<open>(- 1 :: 16 word) mod 42 = 15\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) sdiv 42 = 40\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) sdiv 42 = 65496\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) sdiv - 42 = 65496\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) sdiv - 42 = 40\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) sdiv 1 = 1705\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) sdiv - 1 = 63831\<close>
  by simp

lemma
  \<open>(1 :: 16 word) sdiv 42 = 0\<close>
  by simp

lemma
  \<open>(- 1 :: 16 word) sdiv 42 = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) smod 42 = 25\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) smod 42 = 65511\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) smod - 42 = 25\<close>
  by simp

lemma
  \<open>(- 1705 :: 16 word) smod - 42 = 65511\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) smod 1 = 0\<close>
  by simp

lemma
  \<open>(1705 :: 16 word) smod - 1 = 0\<close>
  by simp

lemma
  \<open>(1 :: 16 word) smod 42 = 1\<close>
  by simp

lemma
  \<open>(- 1 :: 16 word) smod 42 = 65535\<close>
  by simp

text "modulus"

lemma "(27 :: 4 word) = -5" by simp

lemma "(27 :: 4 word) = 11" by simp

lemma "27 \<noteq> (11 :: 6 word)" by simp

text "signed"

lemma "(127 :: 6 word) = -1" by simp

text "number ring simps"

lemma
  "27 + 11 = (38::'a::len word)"
  "27 + 11 = (6::5 word)"
  "7 * 3 = (21::'a::len word)"
  "11 - 27 = (-16::'a::len word)"
  "- (- 11) = (11::'a::len word)"
  "-40 + 1 = (-39::'a::len word)"
  by simp_all

lemma "word_pred 2 = 1" by simp

lemma "word_succ (- 3) = -2" by simp

lemma "23 < (27::8 word)" by simp
lemma "23 \<le> (27::8 word)" by simp
lemma "\<not> 23 < (27::2 word)" by simp
lemma "0 < (4::3 word)" by simp
lemma "1 < (4::3 word)" by simp
lemma "0 < (1::3 word)" by simp

text "ring operations"

lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by simp

text "casting"

lemma "uint (234567 :: 10 word) = 71" by simp
lemma "uint (-234567 :: 10 word) = 953" by simp
lemma "sint (234567 :: 10 word) = 71" by simp
lemma "sint (-234567 :: 10 word) = -71" by simp
lemma "uint (1 :: 10 word) = 1" by simp

lemma "unat (-234567 :: 10 word) = 953" by simp
lemma "unat (1 :: 10 word) = 1" by simp

lemma "ucast (0b1010 :: 4 word) = (0b10 :: 2 word)" by simp
lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by simp
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by simp
lemma "ucast (1 :: 4 word) = (1 :: 2 word)" by simp

text "reducing goals to nat or int and arith:"
lemma "i < x \<Longrightarrow> i < i + 1" for i x :: "'a::len word"
  by unat_arith
lemma "i < x \<Longrightarrow> i < i + 1" for i x :: "'a::len word"
  by unat_arith

text "bit operations"

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by simp
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by simp
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by simp
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by simp
lemma "0 AND 5 = (0 :: 8 word)" by simp
lemma "1 AND 1 = (1 :: 8 word)" by simp
lemma "1 AND 0 = (0 :: 8 word)" by simp
lemma "1 AND 5 = (1 :: 8 word)" by simp
lemma "1 OR 6 = (7 :: 8 word)" by simp
lemma "1 OR 1 = (1 :: 8 word)" by simp
lemma "1 XOR 7 = (6 :: 8 word)" by simp
lemma "1 XOR 1 = (0 :: 8 word)" by simp
lemma "NOT 1 = (254 :: 8 word)" by simp
lemma "NOT 0 = (255 :: 8 word)" by simp

lemma "(-1 :: 32 word) = 0xFFFFFFFF" by simp

lemma "bit (0b0010 :: 4 word) 1" by simp
lemma "\<not> bit (0b0010 :: 4 word) 0" by simp
lemma "\<not> bit (0b1000 :: 3 word) 4" by simp
lemma "\<not> bit (1 :: 3 word) 2" by simp

lemma "bit (0b11000 :: 10 word) n = (n = 4 \<or> n = 3)"
  by (auto simp add: bit_numeral_rec bit_1_iff split: nat.splits)

lemma "set_bit 55 7 True = (183::'a::len word)" by simp
lemma "set_bit 0b0010 7 True = (0b10000010::'a::len word)" by simp
lemma "set_bit 0b0010 1 False = (0::'a::len word)" by simp
lemma "set_bit 1 3 True = (0b1001::'a::len word)" by simp
lemma "set_bit 1 0 False = (0::'a::len word)" by simp
lemma "set_bit 0 3 True = (0b1000::'a::len word)" by simp
lemma "set_bit 0 3 False = (0::'a::len word)" by simp

lemma "odd (0b0101::'a::len word)" by simp
lemma "even (0b1000::'a::len word)" by simp
lemma "odd (1::'a::len word)" by simp
lemma "even (0::'a::len word)" by simp

lemma "\<not> msb (0b0101::4 word)" by simp
lemma   "msb (0b1000::4 word)" by simp
lemma "\<not> msb (1::4 word)" by simp
lemma "\<not> msb (0::4 word)" by simp

lemma "word_cat (27::4 word) (27::8 word) = (2843::'a::len word)"
  by simp
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)"
  by simp

lemma "0b1011 << 2 = (0b101100::'a::len word)" by simp
lemma "0b1011 >> 2 = (0b10::8 word)" by simp
lemma "0b1011 >>> 2 = (0b10::8 word)" by simp
lemma "1 << 2 = (0b100::'a::len word)" apply simp? oops

lemma "slice 3 (0b101111::6 word) = (0b101::3 word)" by simp
lemma "slice 3 (1::6 word) = (0::3 word)" apply simp? oops

lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by simp
lemma "word_roti 2 0b1110 = (0b1011::4 word)" by simp
lemma "word_roti (- 2) 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotr 2 0 = (0::4 word)" by simp
lemma "word_rotr 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_rotl 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_roti (- 2) 1 = (0b0100::4 word)" apply simp? oops

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
proof -
  have "(x AND 0xff00) OR (x AND 0x00ff) = x AND (0xff00 OR 0x00ff)"
    by (simp only: word_ao_dist2)
  also have "0xff00 OR 0x00ff = (-1::16 word)"
    by simp
  also have "x AND -1 = x"
    by simp
  finally show ?thesis .
qed

lemma "word_next (2:: 8 word) = 3" by eval
lemma "word_next (255:: 8 word) = 255" by eval
lemma "word_prev (2:: 8 word) = 1" by eval
lemma "word_prev (0:: 8 word) = 0" by eval

text \<open>singed division\<close>

lemma
  "( 4 :: 32 word) sdiv  4 =  1"
  "(-4 :: 32 word) sdiv  4 = -1"
  "(-3 :: 32 word) sdiv  4 =  0"
  "( 3 :: 32 word) sdiv -4 =  0"
  "(-3 :: 32 word) sdiv -4 =  0"
  "(-5 :: 32 word) sdiv -4 =  1"
  "( 5 :: 32 word) sdiv -4 = -1"
  by (simp_all add: sdiv_word_def signed_divide_int_def)

lemma
  "( 4 :: 32 word) smod  4 =   0"
  "( 3 :: 32 word) smod  4 =   3"
  "(-3 :: 32 word) smod  4 =  -3"
  "( 3 :: 32 word) smod -4 =   3"
  "(-3 :: 32 word) smod -4 =  -3"
  "(-5 :: 32 word) smod -4 =  -1"
  "( 5 :: 32 word) smod -4 =   1"
  by (simp_all add: smod_word_def signed_modulo_int_def signed_divide_int_def)


text \<open>comparison\<close>

lemma "1 < (1024::32 word) \<and> 1 \<le> (1024::32 word)"
  by simp

text "bool lists"

lemma "of_bl [True, False, True, True] = (0b1011::'a::len word)" by simp

lemma "to_bl (0b110::4 word) = [False, True, True, False]" by simp

lemma "of_bl (replicate 32 True) = (0xFFFFFFFF::32 word)"
  by (simp add: numeral_eq_Suc)

text "proofs using bitwise expansion"

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
  by word_bitwise

lemma "(x AND NOT 3) >> 4 << 2 = ((x >> 2) AND NOT 3)"
  for x :: "10 word"
  by word_bitwise

lemma "((x AND -8) >> 3) AND 7 = (x AND 56) >> 3"
  for x :: "12 word"
  by word_bitwise

text "some problems require further reasoning after bit expansion"

lemma "x \<le> 42 \<Longrightarrow> x \<le> 89"
  for x :: "8 word"
  apply word_bitwise
  apply blast
  done

lemma "(x AND 1023) = 0 \<Longrightarrow> x \<le> -1024"
  for x :: \<open>32 word\<close>
  apply word_bitwise
  apply clarsimp
  done

text "operations like shifts by non-numerals will expose some internal list
 representations but may still be easy to solve"

lemma shiftr_overflow: "32 \<le> a \<Longrightarrow> b >> a = 0"
  for b :: \<open>32 word\<close>
  apply word_bitwise
  apply simp
  done

(* testing for presence of word_bitwise *)
lemma "((x :: 32 word) >> 3) AND 7 = (x AND 56) >> 3"
  by word_bitwise

end

end
