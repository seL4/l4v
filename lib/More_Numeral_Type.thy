(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory More_Numeral_Type
  imports "Word_Lib.WordSetup"
begin

(* This theory provides additional setup for numeral types, which should probably go into
   Numeral_Type in the distribution at some point. *)

text \<open>
  The function package uses @{const size} for guessing termination measures.
  Using @{const size} also provides a convenient cast to natural numbers.
\<close>

instantiation num1 :: size
begin
  definition size_num1 where [simp, code]: "size (n::num1) = 0"
  instance ..
end

instantiation bit0 and bit1 :: (finite) size
begin
  definition size_bit0 where [code]: "size n = nat (Rep_bit0 n)"
  definition size_bit1 where [code]: "size n = nat (Rep_bit1 n)"
  instance ..
end

(* As in the parent theory Numeral_Type, we first prove everything abstractly to avoid duplication,
   and then instantiate bit0 and bit1. *)
locale mod_size_order = mod_ring n Rep Abs
  for n :: int
  and Rep :: "'a::{comm_ring_1,size,linorder} \<Rightarrow> int"
  and Abs :: "int \<Rightarrow> 'a::{comm_ring_1,size,linorder}" +
  assumes size_def: "size x = nat (Rep x)"
  assumes less_def: "(a < b) = (Rep a < Rep b)"
  assumes less_eq_def: "(a \<le> b) = (Rep a \<le> Rep b)"
begin

text \<open>
  Automatic simplification of concrete @{term "(<)"} and @{term "(<=)"} goals on numeral types.
\<close>
lemmas order_numeral[simp] =
  less_def[of "numeral a" "numeral b" for a b]
  less_eq_def[of "numeral a" "numeral b" for a b]
  less_def[of "0" "numeral b" for b]
  less_def[of "1" "numeral b" for b]
  less_eq_def[of "0" "numeral b" for b]
  less_eq_def[of "1" "numeral b" for b]
  less_def[of "numeral a" "0" for a]
  less_def[of "numeral a" "1" for a]
  less_eq_def[of "numeral a" "0" for a]
  less_eq_def[of "numeral a" "1" for a]

text \<open> Simplifying size numerals. \<close>
lemmas [simp] = Rep_numeral
lemmas size_numerals[simp] = size_def[of "numeral m" for m]

text \<open> Simplifying representatives of 0 and 1 \<close>
lemmas [simp] = Rep_0 Rep_1

lemmas definitions = definitions less_def less_eq_def size_def

lemmas Rep = type_definition.Rep[OF type]
lemmas Abs_cases = type_definition.Abs_cases[OF type]

lemma of_nat_size[simp]:
  "of_nat (size x) = (x::'a)"
  by (cases x rule: Abs_cases) (clarsimp simp: Abs_inverse of_int_eq size_def)

lemma size_of_nat[simp]:
  "size (of_nat x :: 'a) = x mod n"
  by (simp add: Rep_Abs_mod of_nat_eq size0 size_def)

lemma zero_less_eq[simp]:
  "0 \<le> (x :: 'a)"
  using Rep by (simp add: less_eq_def)

lemma zero_less_one[simp,intro!]:
  "0 < (1::'a)"
  by (simp add: less_def)

lemma zero_least[simp,intro]:
  "(x::'a) < y \<Longrightarrow> 0 < y"
  by (simp add: le_less_trans)

lemma not_less_zero_bit0[simp]:
  "\<not> (x::'a) < 0"
  by (simp add: not_less)

lemmas not_less_zeroE[elim!] = notE[OF not_less_zero]

lemma one_leq[simp]:
  "(1 \<le> x) = (0 < (x::'a))"
  using less_def less_eq_def by auto

lemma less_eq_0[simp]:
  "(x \<le> 0) = (x = (0::'a))"
  by (simp add: antisym)

lemma size_less[simp]:
  "(size (x::'a) < size y) = (x < y)"
  by (cases x rule: Abs_cases, cases y rule: Abs_cases) (auto simp: Abs_inverse definitions)

lemma size_inj[simp]:
  "(size (x::'a) = size y) = (x = y)"
  by (metis of_nat_size)

lemma size_less_eq[simp]:
  "(size (x::'a) \<le> size y) = (x \<le> y)"
  by (auto simp: le_eq_less_or_eq)

lemma size_0[simp]:
  "size (0::'a) = 0"
  by (simp add: size_def)

lemma size_1[simp]:
  "size (1::'a) = 1"
  by (simp add: size_def)

lemma size_eq_0[simp]:
  "(size x = 0) = ((x::'a) = 0)"
  using size_inj by fastforce

lemma minus_less:
  "\<lbrakk> y \<le> x; 0 < y \<rbrakk> \<Longrightarrow> x - y < (x::'a)"
  unfolding definitions
  by (cases x rule: Abs_cases, cases y rule: Abs_cases) (simp add: Abs_inverse)

lemma pred[simp,intro!]:
  "0 < (x::'a) \<Longrightarrow> x - 1 < x"
  by (auto intro!: minus_less)

lemma of_nat_cases[case_names of_nat]:
  "(\<And>m. \<lbrakk> (x::'a) = of_nat m; m < nat n \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis mod_type.Rep_less_n mod_type_axioms nat_mono_iff of_nat_size size0 size_def)

lemma minus_induct[case_names 0 minus]:
  assumes "P (0::'a)"
  assumes suc: "\<And>x. \<lbrakk> P (x - 1); 0 < x \<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof (cases x rule: of_nat_cases)
  case (of_nat m)
  have "P (of_nat m)"
  proof (induct m)
    case 0
    then show ?case using `P 0` by simp
  next
    case (Suc m)
    show ?case
    proof (cases "1 + of_nat m = (0::'a)")
      case True
      then show ?thesis using `P 0` by simp
    next
      case False
      with Suc suc show ?thesis by (metis add_diff_cancel_left' less_eq_0 not_less of_nat_Suc)
    qed
  qed
  with of_nat show ?thesis by simp
qed

lemma plus_induct[case_names 0 plus]:
  assumes "P (0::'a)"
  assumes suc: "\<And>x. \<lbrakk> P x; x < x + 1 \<rbrakk> \<Longrightarrow> P (x + 1)"
  shows "P x"
proof (cases x rule: of_nat_cases)
  case (of_nat m)
  have "P (of_nat m)"
  proof (induct m)
    case 0
    then show ?case using `P 0` by simp
  next
    case (Suc m)
    with `P 0` suc show ?case by (metis diff_add_cancel minus_induct pred)
  qed
  with of_nat show ?thesis by simp
qed

end

interpretation bit0:
  mod_size_order "int CARD('a::finite bit0)"
                 "Rep_bit0 :: 'a::finite bit0 \<Rightarrow> int"
                 "Abs_bit0 :: int \<Rightarrow> 'a::finite bit0"
  by unfold_locales (auto simp: size_bit0_def less_bit0_def less_eq_bit0_def)

interpretation bit1:
  mod_size_order "int CARD('a::finite bit1)"
                 "Rep_bit1 :: 'a::finite bit1 \<Rightarrow> int"
                 "Abs_bit1 :: int \<Rightarrow> 'a::finite bit1"
  by unfold_locales (auto simp: size_bit1_def less_bit1_def less_eq_bit1_def)

declare bit0.minus_induct[induct type]
declare bit1.minus_induct[induct type]

section \<open>Further enumeration instances.\<close>

instantiation bit0 and bit1 :: (finite) enumeration_both
begin

definition enum_alt_bit0 where "enum_alt \<equiv> alt_from_ord (enum :: 'a :: finite bit0 list)"
definition enum_alt_bit1  where "enum_alt \<equiv> alt_from_ord (enum :: 'a :: finite bit1 list)"

instance by intro_classes (auto simp: enum_alt_bit0_def enum_alt_bit1_def)

end


subsection \<open>Relating @{const enum} and @{const size}\<close>

lemma fromEnum_size_bit0[simp]:
  "fromEnum (x::'a::finite bit0) = size x"
proof -
  have "enum ! the_index enum x = x" by (auto intro: nth_the_index)
  moreover
  have "the_index enum x < length (enum::'a bit0 list)" by (auto intro: the_index_bounded)
  moreover
  { fix y
    assume "Abs_bit0' (int y) = x"
    moreover
    assume "y < 2 * CARD('a)"
    ultimately
    have "y = nat (Rep_bit0 x)"
      by (smt Abs_bit0'_code card_bit0 mod_pos_pos_trivial nat_int of_nat_less_0_iff
              zless_nat_eq_int_zless)
  }
  ultimately
  show ?thesis by (simp  add: fromEnum_def enum_bit0_def size_bit0_def)
qed

lemma fromEnum_size_bitq[simp]:
  "fromEnum (x::'a::finite bit1) = size x"
proof -
  have "enum ! the_index enum x = x" by (auto intro: nth_the_index)
  moreover
  have "the_index enum x < length (enum::'a bit1 list)" by (auto intro: the_index_bounded)
  moreover
  { fix y
    assume "Abs_bit1' (int y) = x"
    moreover
    assume "y < Suc (2 * CARD('a))"
    ultimately
    have "y = nat (Rep_bit1 x)"
      by (smt Abs_bit1'_code card_bit1 mod_pos_pos_trivial nat_int of_nat_less_0_iff
              zless_nat_eq_int_zless)
  }
  ultimately
  show ?thesis by (simp add: fromEnum_def enum_bit1_def size_bit1_def del: upt_Suc)
qed

lemma minBound_size_bit0[simp]:
  "(minBound::'a::finite bit0) = 0"
  by (simp add: minBound_def hd_map enum_bit0_def Abs_bit0'_def zero_bit0_def)

lemma minBound_size_bit1[simp]:
  "(minBound::'a::finite bit1) = 0"
  by (simp add: minBound_def hd_map enum_bit1_def Abs_bit1'_def zero_bit1_def)

lemma maxBound_size_bit0[simp]:
  "(maxBound::'a::finite bit0) = of_nat (2 * CARD('a) - 1)"
  by (simp add: maxBound_def enum_bit0_def last_map Abs_bit0'_def bit0.of_nat_eq)

lemma maxBound_size_bit1[simp]:
  "(maxBound::'a::finite bit1) = of_nat (2 * CARD('a))"
  by (simp add: maxBound_def enum_bit1_def last_map Abs_bit1'_def bit1.of_nat_eq)

end