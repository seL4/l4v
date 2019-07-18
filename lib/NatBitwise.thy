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

(* FIXME: MOVE *)
lemma int_2p_eq_shiftl:
  "(2::int)^x = 1 << x"
  by (simp add: shiftl_int_def)

lemma nat_2p_eq_shiftl:
  "(2::nat)^x = 1 << x"
  by (simp add: shiftl_nat_def int_2p_eq_shiftl)

(* FIXME: MOVE? *)
lemma nat_int_mul:
  "nat (int a * b) = a * nat b"
  by (simp add: nat_mult_distrib)

lemma shiftl_nat_alt_def:
  "(x::nat) << n = x * 2^n"
  by (simp add: shiftl_nat_def shiftl_int_def nat_int_mul)

(* FIXME: MOVE *)
lemma int_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: int) << n < y << m) = (x < y << (m - n))"
  apply (drule le_Suc_ex)
  apply (clarsimp simp: shiftl_int_def power_add)
  done

lemma nat_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: nat) << n < y << m) = (x < y << (m - n))"
  by (simp add: nat_int_comparison(2) shiftl_nat_def int_shiftl_less_cancel)

(* FIXME: MOVE *)
lemma int_shiftl_lt_2p_bits:
  "0 \<le> (x::int) \<Longrightarrow> x < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_int_def)
  apply (clarsimp simp: bin_nth_eq_mod even_iff_mod_2_eq_zero)
  apply (drule_tac z="2^i" in less_le_trans)
   apply simp
  apply simp
  done
lemma int_shiftl_lt_2p_bits':
  "0 \<le> (x::int) \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i \<Longrightarrow> x < 1 << n"
  \<comment> \<open>converse is also true, but proof seems annoyingly hard\<close>
  oops

lemma nat_shiftl_lt_2p_bits:
  "(x::nat) < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_nat_def test_bit_nat_def zless_nat_eq_int_zless)
  apply (fastforce dest: int_shiftl_lt_2p_bits[rotated])
  done
lemma nat_shiftl_lt_2p_bits':
  "\<forall>i \<ge> n. \<not> (x::nat) !! i \<Longrightarrow> x < 1 << n"
  oops

(* FIXME: MOVE *)
lemma int_eq_test_bit:
  "((x :: int) = y) = (\<forall>i. test_bit x i = test_bit y i)"
  apply simp
  apply (metis bin_eqI)
  done
lemmas int_eq_test_bitI = int_eq_test_bit[THEN iffD2, rule_format]

lemma nat_eq_test_bit:
  "((x :: nat) = y) = (\<forall>i. test_bit x i = test_bit y i)"
  apply (simp add: test_bit_nat_def)
  apply (metis bin_eqI int_int_eq)
  done
lemmas nat_eq_test_bitI = nat_eq_test_bit[THEN iffD2, rule_format]

end