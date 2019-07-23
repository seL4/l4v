(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(* Instance of bit ops for nat. Used by HaskellLib and AutoCorres.
 * Lemmas about this instance should also go here. *)
theory NatBitwise
imports
  "HOL-Word.Word"
  Lib
begin

instantiation nat :: bit_operations
begin

(* NB: this is not useful, because NOT flips the sign, and hence this
 * definition always produces 0. *)
definition
  "bitNOT = nat o bitNOT o int"

definition
  "bitAND x y = nat (bitAND (int x) (int y))"

definition
  "bitOR x y = nat (bitOR (int x) (int y))"

definition
  "bitXOR x y = nat (bitXOR (int x) (int y))"

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
  apply (clarsimp simp: shiftl_nat_def test_bit_nat_def zless_nat_eq_int_zless)
  apply (fastforce dest: int_shiftl_lt_2p_bits[rotated])
  done

lemma nat_eq_test_bit:
  "((x :: nat) = y) = (\<forall>i. test_bit x i = test_bit y i)"
  apply (simp add: test_bit_nat_def)
  apply (metis bin_eqI int_int_eq)
  done
lemmas nat_eq_test_bitI = nat_eq_test_bit[THEN iffD2, rule_format]

end