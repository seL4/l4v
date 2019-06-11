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

lemma minus1_leq:
  "\<lbrakk> x - 1 \<le> y; y < x \<rbrakk> \<Longrightarrow> (y::'a) = x-1"
  by (smt Rep_1 Rep_Abs_mod Rep_less_n less_def diff_def int_mod_ge le_neq_trans)

lemma max_bound_leq[simp,intro!]:
  "(x::'a) \<le> -1"
  by (smt Rep_1 Rep_Abs_mod Rep_less_n less_eq_def int_mod_ge' minus_def)

lemma leq_minus1_less:
  "0 < y \<Longrightarrow> (x \<le> y - 1) = (x < (y::'a))"
  by (metis le_less less_trans minus1_leq not_less pred)

lemma max_bound_neq_conv[simp]:
  "(x \<noteq> -1) = ((x::'a) < -1)"
  using le_neq_trans by auto

lemma max_bound_leq_conv[simp]:
  "(- 1 \<le> (x::'a)) = (x = - 1)"
  by (simp add: eq_iff)

lemma max_bound_not_less[simp]:
  "\<not> -1 < (x::'a)"
  using minus1_leq by fastforce

lemma minus_1_eq:
  "(-1::'a) = of_nat (nat n - 1)"
  unfolding definitions using Rep_Abs_1 of_nat_eq size1 by auto

lemma n_not_less_Rep[simp]:
  "\<not> n < Rep x"
  using Rep[of x] by (simp add: not_less)

lemma size_plus:
  "(x::'a) < x + y \<Longrightarrow> size (x + y) = size x + size y"
  unfolding definitions Rep_Abs_mod
  using Rep size0
  by (simp flip: nat_add_distrib add: eq_nat_nat_iff pos_mod_sign mod_add_if_z split: if_split_asm)

lemma Suc_size[simp]:
  "(x::'a) < x + 1 \<Longrightarrow> size (x + 1) = Suc (size x)"
  by (simp add: size_plus)

lemma no_overflow_eq_max_bound:
  "((x::'a) < x + 1) = (x < -1)"
  unfolding definitions
  by (smt Rep_Abs_mod Rep_Abs_1 Rep_less_n int_mod_ge int_mod_ge' size0)

lemma plus_one_leq:
  "x < y \<Longrightarrow> x + 1 \<le> (y::'a)"
  by (metis add_diff_cancel_right' leq_minus1_less not_le zero_least)

lemma less_uminus:
  "\<lbrakk> - x < y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> - y < (x::'a)"
  unfolding definitions
  by (smt Rep_inverse Rep_mod Rep_Abs_mod size0 zmod_zminus1_eq_if)

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

lemma from_top_induct[case_names top step]:
  assumes top: "\<And>x. y \<le> x \<Longrightarrow> P (x::'a)"
  assumes step: "\<And>x. \<lbrakk>P x; 0 < x; x \<le> y\<rbrakk> \<Longrightarrow> P (x - 1)"
  shows "P x"
proof -
  obtain z where x: "x = y - z"
    by (metis diff_eq_diff_eq diff_right_commute)
  moreover
  have "P (y - z)"
  proof (induct z rule: plus_induct)
    case 0
    then show ?case by (simp add: top)
  next
    case (plus x)
    then have [simp]: "y - (x + 1) = (y - x) - 1" by simp
    show ?case
    proof (cases "x < y")
      case True
      with plus show ?thesis
       by simp (metis diff_add_cancel eq_iff_diff_eq_0 le_neq_trans step plus_one_leq not_le
                      top zero_less_eq)
    next
      case False
      with plus show ?thesis
       by (smt top Rep_Abs_mod Rep_le_n less_def less_eq_def diff_def int_mod_ge' size0)
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma tranclp_greater: "(>)\<^sup>+\<^sup>+ = ((>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by(auto simp add: fun_eq_iff intro: less_trans elim: tranclp.induct)

lemma card_n:
  "CARD('a) = nat n"
  using type by (simp add: type_definition.card)

lemma finite_UNIV[intro!,simp]:
  "finite (UNIV::'a set)"
  by (rule card_ge_0_finite) (simp add: card_n size0)

lemma finite_greater[simp]:
  "finite {(x, y). y < (x::'a)}"
  by (rule finite_subset[of _ "UNIV \<times> UNIV"], simp)
     (rule finite_cartesian_product; rule finite_UNIV)

lemma wf_greater[intro!,simp]:
  "wf {(x,y). x > (y::'a)}"
  by (auto simp: trancl_def tranclp_greater intro!: finite_acyclic_wf acyclicI)

(* less_induct already instantiated in class well_order *)
lemma greater_induct[case_names greater]:
  "(\<And>x. (\<And>z. x < z \<Longrightarrow> P z) \<Longrightarrow> P x) \<Longrightarrow> P (x::'a)"
  by (rule wf_induct_rule, rule wf_greater) fastforce

lemma from_top_full_induct[case_names top step]:
  assumes top: "\<And>x. y \<le> x \<Longrightarrow> P (x::'a)"
  assumes step: "\<And>x. \<lbrakk>\<forall>z > x. P z; x < y\<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof (induct x rule: greater_induct)
  case (greater x)
  show ?case
  proof (cases "x < y")
    case True
    then show ?thesis by (blast intro: step greater)
  next
    case False
    then show ?thesis by (auto simp: not_less intro: top)
  qed
qed

interpretation greater_wellorder: wellorder "(\<ge>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "(>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  by unfold_locales (auto intro: greater_induct)

lemma greater_least_fold[simp]: "greater_wellorder.Least = Greatest"
  by (auto simp: greater_wellorder.Least_def Greatest_def)

lemmas GreatestI = greater_wellorder.LeastI[simplified greater_least_fold]
lemmas Greatest_le = greater_wellorder.Least_le[simplified greater_least_fold]
lemmas exists_greatest_iff = greater_wellorder.exists_least_iff
lemmas GreatestI2_wellorder = greater_wellorder.LeastI2_wellorder[simplified greater_least_fold]

lemma neq_0_conv:
  "((x::'a) \<noteq> 0) = (0 < x)"
  by (meson neqE not_less_zero_bit0)

lemma minus_leq_less: "\<lbrakk> (x::'a) \<le> y; 0 < z; z \<le> x \<rbrakk> \<Longrightarrow> x - z < y"
  by (metis le_less less_trans minus_less)

lemma minus_one_leq_less: "\<lbrakk> (x::'a) \<le> y; 0 < x \<rbrakk> \<Longrightarrow> x - 1 < y"
  using pred by fastforce

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

lemma maxBound_size_bit0:
  "(maxBound::'a::finite bit0) = of_nat (2 * CARD('a) - 1)"
  by (simp add: maxBound_def enum_bit0_def last_map Abs_bit0'_def bit0.of_nat_eq)

lemma maxBound_size_bit1:
  "(maxBound::'a::finite bit1) = of_nat (2 * CARD('a))"
  by (simp add: maxBound_def enum_bit1_def last_map Abs_bit1'_def bit1.of_nat_eq)

lemma maxBound_minus_one_bit0:
  "maxBound = (-1 ::'a::finite bit0)"
  by (simp add: bit0.definitions bit0.of_nat_eq bit0.Rep_Abs_1 maxBound_size_bit0)

lemma maxBound_minus_one_bit1:
  "maxBound = (-1 ::'a::finite bit1)"
  by (simp add: bit1.definitions bit1.of_nat_eq bit1.Rep_Abs_1 zmod_minus1 maxBound_size_bit1)

lemmas maxBound_size_bit = maxBound_size_bit0 maxBound_size_bit1
lemmas maxBound_minus_one_bit[simp] = maxBound_minus_one_bit1 maxBound_minus_one_bit0

end