(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Padding
imports Main
begin

definition padup :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "padup align n \<equiv> (align - n mod align) mod align"

lemma padup_dvd:
  "0 < b \<Longrightarrow> (padup b n = 0) = (b dvd n)"
  unfolding padup_def
  apply(subst dvd_eq_mod_eq_0)
  apply(subst mod_if [where m="b - n mod b"])
  apply clarsimp
  apply(insert mod_less_divisor [of b n])
  apply arith
  done

lemma dvd_padup_add:
  "0 < x \<Longrightarrow> x dvd y + padup x y"
  apply(clarsimp simp: padup_def)
  apply(subst mod_if [where m="x - y mod x"])
  apply(clarsimp split: if_split_asm)
  apply(rule conjI)
   apply clarsimp
   apply(subst ac_simps)
   apply(subst diff_add_assoc)
    apply(rule mod_less_eq_dividend)
   apply(rule dvd_add)
    apply simp
   apply(subst minus_div_mult_eq_mod[symmetric])
   apply(subst diff_diff_right)
    apply(subst ac_simps)
    apply(subst minus_mod_eq_mult_div[symmetric])
    apply simp
   apply simp
  apply(auto simp: dvd_eq_mod_eq_0)
  done


end
