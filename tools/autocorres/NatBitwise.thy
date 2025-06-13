(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Instance of bit ops for nat.
   Lemmas about this instance should also go here. *)
theory NatBitwise
imports
  Word_Lib.WordSetup
begin

lemma lsb_nat_def:
  \<open>lsb n = lsb (int n)\<close>
  by (simp add: bit_simps)

instantiation nat :: msb
begin

definition
  "msb x = msb (int x)"

instance ..

end

lemma not_msb_nat:
  \<open>\<not> msb n\<close> for n :: nat
  by (simp add: msb_nat_def msb_int_def)

lemma set_bit_nat_def:
  \<open>set_bit x y z = nat (set_bit (int x) y z)\<close>
  by (rule bit_eqI) (simp add: bit_simps bin_sc_pos)

lemma nat_2p_eq_shiftl:
  "(2::nat)^x = 1 << x"
  by simp

lemmas shiftl_nat_alt_def = shiftl_nat_def

lemma nat_int_mul:
  "nat (int a * b) = a * nat b"
  by (simp add: nat_mult_distrib)

lemma shiftl_nat_def:
  "(x::nat) << y = nat (int x << y)"
  by (simp add: nat_int_mul push_bit_eq_mult shiftl_def)

lemma int_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: int) << n < y << m) = (x < y << (m - n))"
  apply (drule le_Suc_ex)
  apply (clarsimp simp: shiftl_int_def power_add)
  done

lemma nat_shiftl_less_cancel:
  "n \<le> m \<Longrightarrow> ((x :: nat) << n < y << m) = (x < y << (m - n))"
  apply (simp add: nat_int_comparison(2) shiftl_nat_def shiftl_def)
  by (metis int_shiftl_less_cancel shiftl_def)


lemma nat_shiftl_lt_2p_bits:
  "(x::nat) < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_nat_def zless_nat_eq_int_zless
                  dest!: le_Suc_ex)
  by (metis bit_take_bit_iff not_add_less1 take_bit_nat_eq_self_iff)

lemmas nat_eq_test_bit = bit_eq_iff
lemmas nat_eq_test_bitI = bit_eq_iff[THEN iffD2, rule_format]

lemma int_2p_eq_shiftl:
  "(2::int)^x = 1 << x"
  by (simp add: shiftl_int_def)

lemma int_shiftl_lt_2p_bits:
  "0 \<le> (x::int) \<Longrightarrow> x < 1 << n \<Longrightarrow> \<forall>i \<ge> n. \<not> x !! i"
  apply (clarsimp simp: shiftl_int_def)
  by (metis bit_take_bit_iff not_less take_bit_int_eq_self_iff)
\<comment> \<open>TODO: The converse should be true as well, but seems hard to prove.\<close>

lemmas int_eq_test_bitI = bin_eq_iff[THEN iffD2, rule_format]

end