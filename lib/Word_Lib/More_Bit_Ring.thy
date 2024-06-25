(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory More_Bit_Ring
  imports Main
begin

(* Additional equalities on semiring_bit_operations and ring_bit_operations, in particular
   relationships between Boolean and arithmetic operations. *)

context semiring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma disjunctive_add2:
  "(x AND y) = 0 \<Longrightarrow> x + y = x OR y"
  by (metis disjunctive_add bit_0_eq bit_and_iff bot_apply bot_bool_def)

end
end

context ring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma not_xor_is_eqv:
  "NOT (x XOR y) = (x AND y) OR (NOT x AND NOT y)"
  by (simp add: bit.xor_def bit.disj_conj_distrib or.commute)

lemma not_xor_eq_xor_not:
  "(NOT x) XOR y = x XOR (NOT y)"
  by simp

lemma not_minus:
  "NOT (x - y) = y - x - 1"
  by (simp add: not_eq_complement)

lemma minus_not_eq_plus_1:
  "- NOT x = x + 1"
  by (simp add: minus_eq_not_plus_1)

lemma not_minus_eq_minus_1:
  "NOT (- x) = x - 1"
  by (simp add: not_eq_complement)

lemma and_plus_not_and:
  "(x AND y) + (x AND NOT y) = x"
  by (metis and.left_commute and.right_neutral bit.conj_cancel_right bit.conj_disj_distrib
            bit.conj_zero_right bit.disj_cancel_right disjunctive_add2)

lemma or_eq_and_not_plus:
  "x OR y = (x AND NOT y) + y"
  by (simp add: and.assoc bit.disj_conj_distrib2 disjunctive_add2)

lemma and_eq_not_or_minus:
  "x AND y = (NOT x OR y) - NOT x"
  by (metis and.idem and_eq_not_not_or eq_diff_eq or.commute or.idem or_eq_and_not_plus)

lemma and_not_eq_or_minus:
  "x AND NOT y = (x OR y) - y"
  by (simp add: or_eq_and_not_plus)

lemma and_not_eq_minus_and:
  "x AND NOT y = x - (x AND y)"
  by (simp add: add.commute eq_diff_eq and_plus_not_and)

lemma or_minus_eq_minus_and:
  "(x OR y) - y = x - (x AND y)"
  by (metis and_not_eq_minus_and and_not_eq_or_minus)

lemma plus_eq_and_or:
  "x + y = (x OR y) + (x AND y)"
  using add_commute local.add.semigroup_axioms or_eq_and_not_plus semigroup.assoc
  by (fastforce simp: and_plus_not_and)

lemma xor_eq_or_minus_and:
  "x XOR y = (x OR y) - (x AND y)"
  by (metis (no_types) bit.de_Morgan_conj bit.xor_def2 bit_and_iff bit_or_iff disjunctive_diff)

lemma not_xor_eq_and_plus_not_or:
  "NOT (x XOR y) = (x AND y) + NOT (x OR y)"
  by (metis (no_types, lifting) not_diff_distrib add.commute bit.de_Morgan_conj bit.xor_def2
                                bit_and_iff bit_or_iff disjunctive_diff)

lemma not_xor_eq_and_minus_or:
  "NOT (x XOR y) = (x AND y) - (x OR y) - 1"
  by (metis not_diff_distrib add.commute minus_diff_eq not_minus_eq_minus_1 not_xor_eq_and_plus_not_or)

lemma plus_eq_xor_plus_carry:
  "x + y = (x XOR y) + 2 * (x AND y)"
  by (metis plus_eq_and_or add.commute add.left_commute diff_add_cancel mult_2 xor_eq_or_minus_and)

lemma plus_eq_or_minus_xor:
  "x + y = 2 * (x OR y) - (x XOR y)"
  by (metis add_diff_cancel_left' diff_diff_eq2 local.mult_2 plus_eq_and_or xor_eq_or_minus_and)

lemma plus_eq_minus_neg:
  "x + y = x - NOT y - 1"
  using add_commute local.not_diff_distrib not_minus
  by auto

lemma minus_eq_plus_neg:
  "x - y = x + NOT y + 1"
  by (simp add: add.semigroup_axioms diff_conv_add_uminus minus_eq_not_plus_1 semigroup.assoc)

lemma minus_eq_and_not_minus_not_and:
  "x - y = (x AND NOT y) - (NOT x AND y)"
  by (metis bit.de_Morgan_conj bit.double_compl not_diff_distrib plus_eq_and_or)

lemma minus_eq_xor_minus_not_and:
  "x - y = (x XOR y) - 2 * (NOT x AND y)"
  by (metis (no_types) bit.compl_eq_compl_iff bit.xor_compl_left not_diff_distrib
                       plus_eq_xor_plus_carry)

lemma minus_eq_and_not_minus_xor:
  "x - y = 2 * (x AND NOT y) - (x XOR y)"
  by (metis and.commute minus_diff_eq minus_eq_xor_minus_not_and xor.commute)

lemma and_one_neq_simps[simp]:
  "x AND 1 \<noteq> 0 \<longleftrightarrow> x AND 1 = 1"
  "x AND 1 \<noteq> 1 \<longleftrightarrow> x AND 1 = 0"
  by (clarsimp simp: and_one_eq)+

end
end

end