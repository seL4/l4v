(*
 *
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory String_Compare
imports Main
begin

(* Speed up string comparisons in Isabelle2016-1.
   We replace simp rule Char_eq_Char_iff with one which normalises in fewer steps. *)

(* Beware that this might reappear during theory merges. *)
declare Char_eq_Char_iff [simp del]

lemma pos_divmod_nat_rel_mult_2:
  assumes "0 \<le> b"
  assumes "divmod_nat_rel a b (q, r)"
  shows "divmod_nat_rel (1 + 2*a) (2*b) (q, 1 + 2*r)"
  using assms unfolding divmod_nat_rel_def by auto

lemma pos_nat_mod_mult_2:
  fixes a b :: nat
  assumes "0 \<le> a"
  shows "(1 + 2 * b) mod (2 * a) = 1 + 2 * (b mod a)"
  using pos_divmod_nat_rel_mult_2 [OF assms divmod_nat_rel]
  by (rule mod_nat_unique)

lemma pos_nat_mod_mult_2_r:
  fixes a b :: nat
  assumes "0 \<le> a"
  shows "(2 * b + 1) mod (2 * a) = 2 * (b mod a) + 1"
  using pos_nat_mod_mult_2 by simp

lemma num_double: "num.Bit0 num.One * n = num.Bit0 n"
  by (metis (no_types, lifting) mult_2 numeral_Bit0 numeral_eq_iff
                                numeral_times_numeral)

lemma num_Bit0_mod_pow2_Suc:
  "numeral (num.Bit0 n) mod (2::nat) ^ Suc i = 2 * (numeral n mod 2 ^ i)"
  by (metis mod_mult_mult1 mult_2 numeral_Bit0 power_Suc)

lemma num_Bit1_mod_pow2_Suc:
  "numeral (num.Bit1 n) mod (2::nat) ^ Suc i = 2 * (numeral n mod 2 ^ i) + 1"
  unfolding power_Suc numeral_Bit1 mult_2[symmetric]
  by (rule pos_nat_mod_mult_2_r) simp

datatype peano = Peano_Z | Peano_S peano

primrec
  peano_of_nat :: "nat \<Rightarrow> peano"
where
  "peano_of_nat 0 = Peano_Z"
| "peano_of_nat (Suc n) = Peano_S (peano_of_nat n)"

fun
  truncate_num :: "peano \<Rightarrow> num \<Rightarrow> num option"
where
  "truncate_num Peano_Z n = None"
| "truncate_num (Peano_S p) num.One = Some num.One"
| "truncate_num (Peano_S p) (num.Bit0 n') = map_option num.Bit0 (truncate_num p n')"
| "truncate_num (Peano_S p) (num.Bit1 n') = Some (case_option num.One num.Bit1 (truncate_num p n'))"

lemma truncate_num:
  "(numeral n :: nat) mod 2 ^ d = case_option 0 numeral (truncate_num (peano_of_nat d) n)"
  proof (induct d arbitrary: n)
    case 0 show ?case by (cases n) auto
  next
    case (Suc d) show ?case
    proof (cases n)
      case One thus ?thesis
        apply simp
        apply (rule mod_less)
        using less_2_cases not_less_eq by fastforce
    next
      case (Bit0 m) thus ?thesis
        unfolding Bit0 Suc num_Bit0_mod_pow2_Suc
        by (clarsimp simp: num_double split: option.splits)
    next
      case (Bit1 m) show ?thesis
        unfolding Bit1 Suc num_Bit1_mod_pow2_Suc
        by (clarsimp simp: num_double split: option.splits)
    qed
  qed

fun
  truncate_num_all_zero :: "peano \<Rightarrow> num \<Rightarrow> bool"
where
  "truncate_num_all_zero Peano_Z n = True"
| "truncate_num_all_zero (Peano_S d) (num.Bit0 n) = truncate_num_all_zero d n"
| "truncate_num_all_zero (Peano_S d) _ = False"

lemma truncate_num_all_zero: "truncate_num_all_zero d n \<longleftrightarrow> truncate_num d n = None"
  by (induct n arbitrary: d; case_tac d; simp)

fun
  truncate_num_compare :: "peano \<Rightarrow> num \<Rightarrow> num \<Rightarrow> bool"
where
  "truncate_num_compare Peano_Z m n = True"
| "truncate_num_compare (Peano_S d) num.One num.One = True"
| "truncate_num_compare (Peano_S d) num.One (num.Bit1 n) = truncate_num_all_zero d n"
| "truncate_num_compare (Peano_S d) (num.Bit1 m) num.One = truncate_num_all_zero d m"
| "truncate_num_compare (Peano_S d) (num.Bit0 m) (num.Bit0 n) = truncate_num_compare d m n"
| "truncate_num_compare (Peano_S d) (num.Bit1 m) (num.Bit1 n) = truncate_num_compare d m n"
| "truncate_num_compare (Peano_S d) num.One (num.Bit0 _) = False"
| "truncate_num_compare (Peano_S d) (num.Bit0 _) num.One = False"
| "truncate_num_compare (Peano_S d) (num.Bit0 _) (num.Bit1 _) = False"
| "truncate_num_compare (Peano_S d) (num.Bit1 _) (num.Bit0 _) = False"

lemma truncate_num_compare:
  "truncate_num_compare d m n \<longleftrightarrow> truncate_num d m = truncate_num d n"
  proof -
    have inj_Bit0: "inj num.Bit0" by (auto intro: injI)
    show ?thesis
      by (induction d m n rule: truncate_num_compare.induct;
          clarsimp simp: truncate_num_all_zero map_option_case
                         inj_eq[OF option.inj_map, OF inj_Bit0]
                  split: option.splits)
  qed

abbreviation
  "peano_8 \<equiv> Peano_S (Peano_S (Peano_S (Peano_S (Peano_S (Peano_S (Peano_S (Peano_S Peano_Z)))))))"

lemma numeral_mod_256:
  "(numeral n :: nat) mod 256 = case_option 0 numeral (truncate_num peano_8 n)"
  proof -
    have "peano_of_nat 8 \<equiv> peano_8" by (simp add: eval_nat_numeral)
    thus ?thesis using truncate_num[where d=8] by simp
  qed

lemma Char_eq_iff_truncate_num_compare [simp]:
  "Char k = Char l \<longleftrightarrow> truncate_num_compare peano_8 k l"
  unfolding Char_eq_Char_iff numeral_mod_256 truncate_num_compare
  by (simp split: option.splits)

end
