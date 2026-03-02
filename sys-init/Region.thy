(*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Region
imports
  "Word_Lib.WordSetup"
  "Lib.Lib"
begin

(* A region is a right-open interval of words, see also the definition list_region *)
type_synonym 'a region = "'a word \<times> 'a word"

definition list_region :: "'a region \<Rightarrow> 'a::len word list" where
  "list_region region \<equiv>
     if fst region < snd region then [fst region .e. snd region - 1] else []"

definition length_region :: "'a::len region \<Rightarrow> nat" where
  "length_region region \<equiv>
     if fst region < snd region then unat (snd region - fst region) else 0"

definition take_region :: "nat \<Rightarrow> 'a region \<Rightarrow> 'a::len region" where
  "take_region n region \<equiv>
     if n < length_region region
     then (fst region, fst region + of_nat n)
     else region"

abbreviation list_take_region :: "nat \<Rightarrow> 'a region \<Rightarrow> 'a::len word list" where
  "list_take_region n region \<equiv> list_region (take_region n region)"

abbreviation zip_region :: "'a list \<Rightarrow> 'b region \<Rightarrow> ('a \<times> 'b::len word) list" where
  "zip_region ls region \<equiv> zip ls (list_take_region (length ls) region)"

definition drop_region :: "nat \<Rightarrow> 'a region \<Rightarrow> 'a::len region" where
  "drop_region n region \<equiv>
     if n \<le> length_region region
     then (fst region + of_nat n, snd region)
     else (snd region, snd region)"

abbreviation drop_region' :: "'a list \<Rightarrow> 'b region \<Rightarrow> 'b::len region" where
  "drop_region' ls region \<equiv> drop_region (length ls) region"

abbreviation set_region :: "'a region \<Rightarrow> 'a::len word set" where
  "set_region region \<equiv> set (list_region region)"

lemma set_region_set:
  "set_region region = {fst region ..< snd region}"
  unfolding list_region_def
  apply (cases "fst region < snd region"; clarsimp)
  apply (rule subset_antisym; clarsimp simp: word_le_minus_one_leq)
  apply (meson le_m1_iff_lt word_le_minus_one_leq)
  done

lemma distinct_list_region[simp]:
  "distinct (list_region region)"
  by (clarsimp simp: list_region_def)

lemma take_region_all[simp]:
  "length_region region \<le> n \<Longrightarrow> take_region n region = region"
  by (clarsimp simp: take_region_def)

lemma take_upto_enum:
  "\<lbrakk>0 < n; unat i + n \<le> Suc (unat m)\<rbrakk> \<Longrightarrow> take n [i .e. m] = [i .e. i + of_nat n - 1]"
  apply (clarsimp simp: upto_enum_def take_map simp del: upt_Suc)
  apply (case_tac n; clarsimp simp del: upt_Suc)
  apply (metis (no_types, opaque_lifting) add_leE le_unat_uoi word_arith_nat_add)
  done

lemma take_list_region[simp]:
  "list_region (take_region n region) = take n (list_region region)"
  apply (clarsimp simp: take_region_def list_region_def length_region_def)
  apply safe
    apply (subst take_upto_enum)
      using not_le apply fastforce
     apply unat_arith
    apply clarsimp
   apply (rule sym, clarsimp)
  apply (smt (verit, del_insts) add_0 add_diff_cancel_left' bot_nat_0.not_eq_extremum
                                diff_add_cancel diff_numeral_special(9) le_unat_uoi less_diff_conv
                                order_less_imp_le unat_sub unsigned_0 word_less_nat_alt word_random)
  apply (subst take_all; clarsimp)
  apply (metis Suc_unat_minus_one not_le unat_sub word_le_less_eq word_zero_le)
  done

lemma take_take_region[simp]:
  "take_region n (take_region m region) = take_region (min n m) region"
  apply (clarsimp simp: take_region_def length_region_def)
  apply (smt (verit, ccfv_SIG) add.commute add_cancel_left_right diff_add_cancel le_unat_uoi min_def
                               min_less_iff_conj not_less_iff_gr_or_eq word_of_nat_less word_random)
  done

lemma length_take_region[simp]:
  "length_region (take_region n region) = min (length_region region) n"
  apply (clarsimp simp: length_region_def take_region_def)
  apply (smt (verit, del_insts) add.commute add_cancel_left_right diff_add_cancel le_unat_uoi
                                order_less_le unsigned_0 word_of_nat_less word_random)
  done

\<comment> \<open>FIXME: move to Word_Lib\<close>
lemma drop_upto_enum':
  "unat i + n \<le> unat (m + 1) \<Longrightarrow> drop n [i .e. m] = [i + of_nat n .e. m]"
  apply (clarsimp simp: upto_enum_def drop_map simp del: upt_Suc)
  apply (case_tac n; clarsimp simp del: upt_Suc)
  by (metis add_Suc_right add_leE le_unat_uoi plus_1_eq_Suc unat_1 word_arith_nat_add)

lemma list_drop_region[simp]:
  "list_region (drop_region n region) = drop n (list_region region)"
  apply (case_tac "n = length_region region")
   apply (clarsimp simp: length_region_def list_region_def drop_region_def)
   apply unat_arith
  apply (clarsimp simp: drop_region_def list_region_def length_region_def
                 split: if_split_asm)
  apply safe
    apply (subst drop_upto_enum')
     apply unat_arith
    apply clarsimp
   apply (drule (1) le_neq_implies_less)
   apply (drule word_of_nat_less)
   apply unat_arith
  apply clarsimp
  apply unat_arith
  done

lemma length_region_length[simp]:
  "length (list_region region) = length_region region"
  apply (clarsimp simp: length_region_def list_region_def)
  apply unat_arith
  done

lemma length_region_drop[simp]:
  "length_region (drop_region n region) = length_region region - n"
  by (metis length_code length_drop length_region_length list_drop_region)

lemma list_region_less_all:
  "snd region \<le> m \<Longrightarrow> list_all (\<lambda>n. n < m) (list_region region)"
  apply (clarsimp simp: list_region_def upto_enum_word list_all_def length_region_def)
  apply (metis (no_types, opaque_lifting) le_m1_iff_lt less_irrefl less_le_trans linear
                                          word_of_nat_less word_unat.Rep_inverse)
  done

lemma list_region_singleton[simp]:
  "x < y \<Longrightarrow> list_region (x, x + 1) = [x]"
  by (clarsimp simp: list_region_def)
     unat_arith

(* Append two contiguous regions. Produces a too large region if input is not contiguous, see
   valid_concat_regions for check. *)
definition append_region :: "'a region \<Rightarrow> 'a region \<Rightarrow> 'a::len region" (infixr "@2" 65) where
  "append_region region region' \<equiv>
     if fst region < snd region then (fst region, snd region') else region'"

definition valid_region :: "'a::len region \<Rightarrow> bool" where
  "valid_region region \<equiv> fst region \<le> snd region"

definition valid_concat_regions :: "'a region \<Rightarrow> 'a::len region \<Rightarrow> bool" where
  "valid_concat_regions region region' \<equiv>
     valid_region region \<and> valid_region region' \<and> fst region' = snd region"

lemmas valid_concat_regions_defs = valid_concat_regions_def valid_region_def

lemma valid_concat_regions_valid_regionE[elim!]:
  "valid_concat_regions region region' \<Longrightarrow> valid_region region"
  "valid_concat_regions region region' \<Longrightarrow> valid_region region'"
  by (clarsimp simp: valid_concat_regions_defs)+

lemma append_region_valid_concat_regions[intro!]:
  "\<lbrakk>valid_concat_regions region region'; valid_concat_regions region' region''\<rbrakk> \<Longrightarrow>
   valid_concat_regions region (region' @2 region'')"
  by (clarsimp simp: append_region_def valid_concat_regions_defs)
     unat_arith

lemma valid_append_region[elim!]:
  "valid_concat_regions region region' \<Longrightarrow> valid_region (region @2 region')"
  by (clarsimp simp: append_region_def valid_concat_regions_defs)
     unat_arith

lemma length_append_region[simp]:
  "valid_concat_regions region region' \<Longrightarrow>
   length_region (region @2 region') = length_region region + length_region region'"
  by (clarsimp simp: append_region_def length_region_def valid_concat_regions_defs)
     unat_arith

lemma upto_enum_append_word: (* FIXME: move to Word_lib *)
  "\<lbrakk> i < j; j \<le> k \<rbrakk> \<Longrightarrow> [i .e. k] = [i .e. j-1] @ [j .e. k]"
  for i j k :: "'a::len word"
  unfolding upto_enum_word
  apply (subst map_upt_append[where x="unat j"])
    apply unat_arith
   apply unat_arith
  apply (metis Suc_unat_minus_one not_le word_zero_le)
  done

lemma list_append_region[simp]:
  "valid_concat_regions region region' \<Longrightarrow>
   list_region (region @2 region') = list_region region @ list_region region'"
  apply (clarsimp simp: append_region_def valid_concat_regions_defs list_region_def)
  apply (subst upto_enum_append_word[symmetric])
    apply clarsimp
   apply unat_arith
  apply simp
  done

lemma drop_append_region[simp]:
  "valid_concat_regions region region' \<Longrightarrow>
   drop_region n (region @2 region') =
   drop_region n region @2 drop_region (n - length_region region) region'"
  apply (clarsimp simp: drop_region_def append_region_def length_region_def
                        valid_concat_regions_defs)
  apply (smt (verit, ccfv_threshold) Word.of_nat_unat add_diff_cancel_left' le_unat_uoi
                                     linorder_not_less nless_le of_nat_diff of_nat_le_iff
                                     uint_sub_lem word_less_def)
  done

lemma drop_region_0[simp]:
  "drop_region 0 = (\<lambda>x. x)"
  unfolding drop_region_def
  by clarsimp

lemma drop_region_all:
  "\<lbrakk> valid_region region; length_region region \<le> n \<rbrakk> \<Longrightarrow>
   drop_region n region = (snd region, snd region)"
  by (clarsimp simp: drop_region_def valid_region_def length_region_def)

lemma valid_concat_regions_empty_first[intro!]:
  "valid_concat_regions region region' \<Longrightarrow> valid_concat_regions (snd region, snd region) region'"
  by (clarsimp simp: append_region_def valid_concat_regions_defs)

lemma append_region_empty[simp]:
  "valid_concat_regions (x, x) region \<Longrightarrow> (x, x) @2 region = region"
  by (clarsimp simp: append_region_def prod.expand valid_concat_regions_defs)

end
