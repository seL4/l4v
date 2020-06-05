(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Instance of bit ops for nat. Used by HaskellLib and AutoCorres.
 * Lemmas about this instance should also go here. *)
theory NatBitwise
imports
  Lib
begin

instantiation nat :: bit_operations
begin

definition
  "shiftl x y = nat (shiftl (int x) y)"

definition
  "shiftr x y = nat (shiftr (int x) y)"

definition
  "test_bit x y = test_bit (int x) y"

definition
  "lsb x = lsb (int x)"

definition
  "msb x = msb (int x)"

definition
  "set_bit x y z = nat (set_bit (int x) y z)"

instance ..

end

lemma nat_2p_eq_shiftl:
  "(2::nat)^x = 1 << x"
  by (simp add: shiftl_nat_def int_2p_eq_shiftl)

lemma shiftl_nat_alt_def:
  "(x::nat) << n = x * 2^n"
  by (simp add: shiftl_nat_def shiftl_int_def nat_int_mul)

lemma nat_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: nat) << n < y << m) = (x < y << (m - n))"
  by (simp add: nat_int_comparison(2) shiftl_nat_def int_shiftl_less_cancel)

lemma nat_shiftl_lt_2p_bits:
  "(x::nat) < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_nat_def test_bit_nat_def zless_nat_eq_int_zless shiftl_eq_push_bit
    push_bit_of_1 bit_def power_add zdiv_zmult2_eq dest!: le_Suc_ex)
  done

lemma nat_eq_test_bit:
  "((x :: nat) = y) = (\<forall>i. test_bit x i = test_bit y i)"
  apply (simp add: test_bit_nat_def bit_eq_iff)
  done
lemmas nat_eq_test_bitI = nat_eq_test_bit[THEN iffD2, rule_format]

end