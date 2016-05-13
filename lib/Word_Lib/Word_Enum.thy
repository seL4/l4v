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
  "(enum_class.enum :: ('a :: len) word list) \<equiv> map of_nat [0 ..< 2 ^ len_of TYPE('a)]"

definition
  "enum_class.enum_all (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

instance
  apply (intro_classes)
     apply (simp add: enum_word_def)
     apply force
    apply (simp add: distinct_map enum_word_def)
    apply (rule subset_inj_on, rule word_unat.Abs_inj_on)
    apply (clarsimp simp add: unats_def)
   apply (simp add: enum_all_word_def)
  apply (simp add: enum_ex_word_def)
  done

end

lemma fromEnum_unat[simp]: "fromEnum (x :: ('a :: len) word) = unat x"
  apply (subgoal_tac "x \<in> set enum")
   defer
   apply simp
  apply (unfold fromEnum_def enum_word_def)
  apply (subgoal_tac "ALL n. n < 2 ^ len_of TYPE('a) --> (map of_nat [0..< 2 ^ len_of TYPE('a)] ! n) = x --> n = unat x")
   apply (subgoal_tac "(map of_nat [0..< 2 ^ len_of TYPE('a)]) ! (the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x) = x")
    apply (subgoal_tac "the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x < 2 ^ len_of TYPE('a)")
     apply simp
    apply (subgoal_tac "the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x < length (map of_nat [0..< 2 ^ len_of TYPE('a)])")
     apply simp
    apply (rule the_index_bounded)
    apply (simp add: enum_word_def)
   apply (rule nth_the_index)
   apply (simp add: enum_word_def)
  apply safe
  apply (simp add: unat_of_nat)
  done

lemma length_word_enum: "length (enum :: ('a :: len) word list) = 2 ^ len_of TYPE('a)"
  apply (simp add: enum_word_def)
  done

lemma toEnum_of_nat[simp]: "n < 2 ^ len_of TYPE('a) \<Longrightarrow> ((toEnum n) :: ('a :: len) word) = of_nat n"
  apply (subst toEnum_def)
  apply (simp add: length_word_enum)
  apply (subst enum_word_def)
  apply simp
  done

declare of_nat_diff [simp]

lemma "(maxBound :: ('a :: len) word) = -1"
  apply (unfold maxBound_def enum_word_def)
  apply (subst last_map)
   apply simp
  apply simp
  done

lemma "(minBound :: ('a :: len) word) = 0"
  apply (unfold minBound_def enum_word_def)
  apply (simp add: hd_conv_nth)
  done

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
  apply (subst maxBound_word)
  apply (subst max_word_minus [symmetric])
  apply (rule refl)
  done

lemma leq_maxBound [simp]:
  "(x::'a::len word) \<le> maxBound"
  by (simp add: maxBound_max_word)

end
