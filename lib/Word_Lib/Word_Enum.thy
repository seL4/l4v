(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Author: Thomas Sewell *)

section "Enumeration Instances for Words"

theory Word_Enum
imports Enumeration Word_Lib
begin

instantiation word :: (len) enum
begin

definition
  "(enum_class.enum :: ('a :: len) word list) \<equiv> map of_nat [0 ..< 2 ^ LENGTH('a)]"

definition
  "enum_class.enum_all (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

instance
  apply (intro_classes)
     apply (force simp: enum_word_def)
    apply (simp add: distinct_map enum_word_def)
    apply (rule subset_inj_on, rule word_unat.Abs_inj_on)
    apply (clarsimp simp add: unats_def)
   apply (simp add: enum_all_word_def)
  apply (simp add: enum_ex_word_def)
  done

end

lemma fromEnum_unat[simp]: "fromEnum (x :: 'a::len word) = unat x"
proof -
  have "enum ! the_index enum x = x" by (auto intro: nth_the_index)
  moreover
  have "the_index enum x < length (enum::'a::len word list)" by (auto intro: the_index_bounded)
  moreover
  { fix y assume "of_nat y = x"
    moreover assume "y < 2 ^ LENGTH('a)"
    ultimately have "y = unat x" using of_nat_inverse by fastforce
  }
  ultimately
  show ?thesis by (simp add: fromEnum_def enum_word_def)
qed

lemma length_word_enum: "length (enum :: 'a :: len word list) = 2 ^ LENGTH('a)"
  by (simp add: enum_word_def)

lemma toEnum_of_nat[simp]: "n < 2 ^ LENGTH('a) \<Longrightarrow> (toEnum n :: 'a :: len word) = of_nat n"
  by (simp add: toEnum_def length_word_enum enum_word_def)

declare of_nat_diff [simp]

instantiation word :: (len) enumeration_both
begin

definition
  enum_alt_word_def: "enum_alt \<equiv> alt_from_ord (enum :: ('a :: len) word list)"

instance
  by (intro_classes, simp add: enum_alt_word_def)

end

definition
  upto_enum_step :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word list" ("[_ , _ .e. _]")
where
  "upto_enum_step a b c \<equiv>
      if c < a then [] else map (\<lambda>x. a + x * (b - a)) [0 .e. (c - a) div (b - a)]"
  (* in the wraparound case, bad things happen. *)

lemma maxBound_word:
  "(maxBound::'a::len word) = -1"
  by (simp add: maxBound_def enum_word_def last_map)

lemma minBound_word:
  "(minBound::'a::len word) = 0"
  by (simp add: minBound_def enum_word_def upt_conv_Cons)

lemma maxBound_max_word:
  "(maxBound::'a::len word) = max_word"
  by (simp add: maxBound_word max_word_minus [symmetric])

lemma leq_maxBound [simp]:
  "(x::'a::len word) \<le> maxBound"
  by (simp add: maxBound_max_word)

end
