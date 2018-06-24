(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Verifying quicksort implementation using AutoCorres!
 *)
theory Quicksort
imports
  "AutoCorres.AutoCorres"
  "HOL-Library.Multiset"
begin

declare validNF_whileLoop_inv_measure_twosteps [wp]
declare validNF_whileLoopE_inv_measure_twosteps [wp]

declare creturn_def [vcg_simp]

external_file "quicksort.c"
install_C_file "quicksort.c"
autocorres "quicksort.c"

context quicksort begin

thm partition_body_def
thm quicksort_body_def

thm partition'_def
thm quicksort'.simps


(* Some rules for pointer addition *)

(* FIXME: move *)
lemma ptr_add_assoc [simp]:
  "p +\<^sub>p (i + j) = p +\<^sub>p i +\<^sub>p j"
  by (simp add: CTypesDefs.ptr_add_def distrib_right)

(* FIXME: move *)
lemma ptr_add_commute [simp]:
  "p +\<^sub>p i +\<^sub>p j = p +\<^sub>p j +\<^sub>p i"
  by (metis ptr_add_assoc add.commute)


(*
 * Array validity definitions
 *)

definition
  array_loc_valid :: "word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "array_loc_valid a n \<equiv>
   (unat (ptr_val a) + size_of TYPE(word32) * n \<le> 2 ^ len_of TYPE(addr_bitsize))"

fun
  array_elems_valid :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "array_elems_valid s a 0 = True" |
  "array_elems_valid s a (Suc n) = (is_valid_w32 s a \<and> array_elems_valid s (a +\<^sub>p 1) n)"

lemma array_all_elems_valid:
  (* equivalent characterisation of array validity *)
  "array_elems_valid s a n = (\<forall>m. m < n \<longrightarrow> is_valid_w32 s (a +\<^sub>p int m))"
  apply (induct n arbitrary: a)
   apply simp
  apply (case_tac "n = 0")
   apply simp
  apply (rule iffI)
   apply clarsimp
   apply (case_tac "m = 0")
    apply simp
   apply (case_tac "m = n")
    apply clarsimp
    apply (drule_tac x = "n - 1" in spec)
    apply (simp add: CTypesDefs.ptr_add_def)
   apply (drule_tac x = "m - 1" in spec)
   apply (simp add: CTypesDefs.ptr_add_def)
  apply simp
  apply (frule_tac x = "0" in spec)
  apply clarsimp
  apply (frule_tac x = "m + 1" in spec)
  apply simp
  done

definition
  is_array :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_array s a n \<equiv> (array_loc_valid a n \<and> array_elems_valid s a n)"

(* Necessary condition for many pointer comparison lemmas *)
definition array_not_at_mem_end :: "word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "array_not_at_mem_end a n \<equiv>
   (unat (ptr_val a) + size_of TYPE(word32) * n < 2 ^ len_of TYPE(addr_bitsize))"
  (* same as "array_loc_valid a n" but excluding equality *)


(* Some obvious but useful corollaries *)

lemma array_valid_elem:
  "\<lbrakk> is_array s a n; m < n \<rbrakk> \<Longrightarrow> is_valid_w32 s (a +\<^sub>p int m)"
  by (metis is_array_def array_all_elems_valid)

lemma array_valid_elem2:
  "\<lbrakk> is_array s a (unat n); m < n \<rbrakk> \<Longrightarrow> is_valid_w32 s (a +\<^sub>p uint m)"
  by (metis array_valid_elem uint_nat word_less_nat_alt)

lemma empty_array_is_array:
  "is_array s a 0"
  apply (insert unat_lt2p[of "ptr_val a"])
  apply (simp add: is_array_def array_loc_valid_def)
  done

lemma empty_array_not_at_mem_end:
  "array_not_at_mem_end a 0"
  apply (insert unat_lt2p[of "ptr_val a"])
  apply (simp add: array_not_at_mem_end_def)
  done

lemma subarray_not_at_mem_end1:
  "\<lbrakk> array_loc_valid a n; m < n \<rbrakk> \<Longrightarrow> array_not_at_mem_end a m"
  by (simp add: array_loc_valid_def array_not_at_mem_end_def)

lemma subarray_not_at_mem_end2:
  "\<lbrakk> is_array s a n; m < n \<rbrakk> \<Longrightarrow> array_not_at_mem_end a m"
  by (clarsimp simp: is_array_def subarray_not_at_mem_end1)

lemma updated_array_elems_valid [simp]:
  "array_elems_valid (heap_w32_update f s) a n = array_elems_valid s a n"
  by (induct n arbitrary: a, auto)

lemma updated_array_is_array [simp]:
  "is_array (heap_w32_update f s) a n = is_array s a n"
  by (simp add: is_array_def)


(* Some word arithmetic *)

(* FIXME: move *)
lemma unat_plus_weak:
  "(x::addr) \<le> x + y \<Longrightarrow> unat (x + y) = unat x + unat y"
  by (simp add: unat_plus_simple)

lemma unat_linear_over_array_loc:
  "array_not_at_mem_end a n \<Longrightarrow>
   unat (ptr_val a + of_nat (size_of TYPE(word32)) * (of_nat n)) =
   unat (ptr_val a) + size_of TYPE(word32) * n"
  apply (simp add: array_not_at_mem_end_def)
  apply (subgoal_tac "unat (4 * (of_nat n)) = 4 * n")
   apply (subst unat_plus_weak)
    apply (subst no_olen_add_nat)
    apply (rule_tac s = "4 * n" and t = "unat (4 * of_nat n)" in subst)
     apply (erule sym)
    apply simp+
  apply (simp add: unat_mult_simple unat_of_nat_eq)
  done

lemma unat_linear_over_array_loc2:
  "array_not_at_mem_end a n \<Longrightarrow>
   unat (ptr_val a + 4 * (of_nat n)) = unat (ptr_val a) + 4 * n"
  by (frule unat_linear_over_array_loc, simp)


(* Pointer inequalities *)

lemma array_no_wrap:
  "\<lbrakk> array_loc_valid a n; m < n \<rbrakk> \<Longrightarrow> a \<le> a +\<^sub>p int m"
  apply (clarsimp simp: array_loc_valid_def CTypesDefs.ptr_add_def
                        ptr_le_def' ptr_le_def)
  apply (subst no_olen_add_nat)
  apply (subst unat_mult_simple)
   apply (subst unat_of_nat_eq, simp+)+
  done

lemma array_no_wrap2:
  "\<lbrakk> array_loc_valid a (unat n); m < n \<rbrakk> \<Longrightarrow> a \<le> a +\<^sub>p uint m"
  by (metis array_no_wrap uint_nat word_less_nat_alt)

lemma array_loc_mono:
  "\<lbrakk> array_not_at_mem_end a n; m \<le> n \<rbrakk> \<Longrightarrow> a +\<^sub>p int m \<le> a +\<^sub>p int n"
  apply (clarsimp simp: array_not_at_mem_end_def CTypesDefs.ptr_add_def
                        ptr_le_def' ptr_le_def)
  apply (rule word_plus_mono_right)
   apply (rule word_mult_le_mono1)
     apply (rule PackedTypes.of_nat_mono_maybe_le, simp+)
   apply (subst unat_of_nat_eq, simp+)
  apply (subst no_olen_add_nat)
  apply (subst unat_mult_simple)
   apply (subst unat_of_nat_eq, simp+)+
  done

lemma array_loc_mono2:
  "\<lbrakk> array_not_at_mem_end a (unat n); m \<le> n \<rbrakk> \<Longrightarrow> a +\<^sub>p uint m \<le> a +\<^sub>p uint n"
  by (metis array_loc_mono uint_nat word_le_nat_alt)

lemma array_loc_strict_mono:
  "\<lbrakk> array_not_at_mem_end a n; m < n \<rbrakk> \<Longrightarrow> a +\<^sub>p int m < a +\<^sub>p int n"
  apply (clarsimp simp: array_not_at_mem_end_def CTypesDefs.ptr_add_def
                        ptr_less_def' ptr_less_def)
  apply (rule word_plus_strict_mono_right)
   apply (rule word_mult_less_mono1)
     apply (subst of_nat_mono_maybe, simp+)
   apply (subst unat_of_nat_eq, simp+)
  apply (subst no_olen_add_nat)
  apply (subst unat_mult_simple)
   apply (subst unat_of_nat_eq, simp+)+
  done

lemma array_loc_strict_mono2:
  "\<lbrakk> array_not_at_mem_end a (unat n); m < n \<rbrakk> \<Longrightarrow> a +\<^sub>p uint m < a +\<^sub>p uint n"
  by (metis array_loc_strict_mono uint_nat word_less_nat_alt)


(* Concatenation lemmas *)

lemma array_concat_elems_valid:
  "array_elems_valid s a (n + m) =
   (array_elems_valid s a n \<and> array_elems_valid s (a +\<^sub>p int n) m)"
  apply (subst array_all_elems_valid)+
  apply (rule iffI)
   apply clarsimp
   apply (frule_tac x = "n + ma" in spec)
   apply simp
  apply clarsimp
  apply (case_tac "ma < n")
   apply simp
  apply (frule_tac x = "ma - n" and
                   P = "\<lambda>ma. (ma < m \<longrightarrow> is_valid_w32 s (a +\<^sub>p int ma +\<^sub>p int n))"
                   in spec)
  apply (subgoal_tac "ma - n < m")
   apply (simp add: CTypesDefs.ptr_add_def)
  apply simp
  done

lemma is_array_concat:
  "\<lbrakk> m = 0 \<or> array_not_at_mem_end a n \<rbrakk> \<Longrightarrow>
   is_array s a (n + m) = (is_array s a n \<and> is_array s (a +\<^sub>p int n) m)"
  apply (erule disjE)
   apply (simp add: empty_array_is_array)
  apply (frule unat_linear_over_array_loc)
  apply (subgoal_tac "array_loc_valid a n")
   apply (simp add: is_array_def array_loc_valid_def
                    array_concat_elems_valid add.assoc conj_commute)
  apply (simp add: array_loc_valid_def array_not_at_mem_end_def)
  done

lemma is_array_concat2:
  "\<lbrakk> m \<le> n; array_not_at_mem_end a m \<or> m = n \<rbrakk> \<Longrightarrow>
   is_array s a n = (is_array s a m \<and> is_array s (a +\<^sub>p int m) (n - m))"
  apply (subst diff_add_inverse[symmetric, where n = "m"])
  apply (subst diff_add_assoc, assumption)
  apply (rule is_array_concat, force)
  done

lemma subarray1_is_array:
  "\<lbrakk> is_array s a n; m \<le> n \<rbrakk> \<Longrightarrow> is_array s a m"
  apply (case_tac "m = n", simp)
  apply (frule_tac m = "m" in subarray_not_at_mem_end2, simp)
  apply (simp add: is_array_concat2)
  done

lemma subarray2_is_array:
  "\<lbrakk> is_array s a n; m \<le> n; array_not_at_mem_end a m \<or> m = n \<rbrakk> \<Longrightarrow>
   is_array s (a +\<^sub>p int m) (n - m)"
  by (simp add: is_array_concat2)

lemma concat_is_array:
  "\<lbrakk> is_array s a m; is_array s (a +\<^sub>p int m) (n - m);
     m \<le> n; array_not_at_mem_end a m \<or> m = n \<rbrakk> \<Longrightarrow>
   is_array s a n"
  by (subst is_array_concat2[where m = "m"], simp_all)


(* Array contents, definitions and lemmas *)

primrec
  the_array :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> word32 list"
where
  "the_array s a 0 = []" |
  "the_array s a (Suc n) = (heap_w32 s a) # (the_array s (a +\<^sub>p 1) n)"

lemma the_array_length [simp]:
  "length (the_array s a n) = n"
  by (induct n arbitrary: a, auto)

lemma the_array_elem:
  "m < n \<Longrightarrow> the_array s a n ! m = heap_w32 s (a +\<^sub>p int m)"
  apply (induct n arbitrary: a m)
   apply simp
  apply (case_tac "m = 0")
   apply (auto simp: CTypesDefs.ptr_add_def)
  done

lemma the_arrays_equal:
  "(the_array s a n = the_array s' a' n) =
   (\<forall>m < n. heap_w32 s (a +\<^sub>p int m) = heap_w32 s' (a' +\<^sub>p int m))"
  by (simp add: list_eq_iff_nth_eq the_array_elem)

lemma the_array_concat:
  "the_array s a (n + m) = the_array s a n @ the_array s (a +\<^sub>p int n) m"
  by (induct n arbitrary: a m, auto)

lemma the_array_concat2:
  "m \<le> n \<Longrightarrow>
   the_array s a n = the_array s a m @ the_array s (a +\<^sub>p int m) (n - m)"
  apply (subst diff_add_inverse[symmetric, where n = "m"])
  apply (subst diff_add_assoc)
  apply (simp_all only: the_array_concat)
  done


(* Pointer simplification rules *)

(* FIXME: move *)
lemma word32_mult_cancel_right:
  fixes a :: "addr" and b :: "addr" and c :: "addr"
  shows
  "\<lbrakk> unat a * unat c < 2 ^ len_of TYPE(addr_bitsize);
     unat b * unat c < 2 ^ len_of TYPE(addr_bitsize); c \<noteq> 0 \<rbrakk> \<Longrightarrow>
   (a * c = b * c) = (a = b)"
  apply (rule iffI)
   apply simp_all
  apply (subgoal_tac "a = a * c div c")
   apply simp
   apply (rule sym)
   apply (rule Word.word_div_mult[symmetric, where 'a = addr_bitsize],
          unat_arith, simp)+
  done

lemma ptr_offsets_eq [simp]:
  fixes i :: "nat" and j :: "nat" and a :: "word32 ptr"
  shows
  "\<lbrakk> i * size_of TYPE(word32) < 2 ^ len_of TYPE(addr_bitsize);
     j * size_of TYPE(word32) < 2 ^ len_of TYPE(addr_bitsize) \<rbrakk> \<Longrightarrow>
   (a +\<^sub>p int i = a +\<^sub>p int j) = (i = j)"
  by (simp add: CTypesDefs.ptr_add_def word32_mult_cancel_right
                unat_of_nat_eq of_nat_inj)

lemma ptr_offsets_eq2 [simp]:
  fixes i :: "addr" and j :: "addr" and a :: "word32 ptr"
  shows
  "\<lbrakk> unat i * size_of TYPE(word32) < 2 ^ len_of TYPE(addr_bitsize);
     unat j * size_of TYPE(word32) < 2 ^ len_of TYPE(addr_bitsize) \<rbrakk> \<Longrightarrow>
   (a +\<^sub>p uint i = a +\<^sub>p uint j) = (i = j)"
  by (simp add: uint_nat)


(* Array update simplification *)

(* FIXME: move? *)
lemma trivial_heap_update [simp]:
  "heap_w32_update (\<lambda>x. x) s = s"
  by simp

lemma the_updated_array:
  "\<lbrakk> is_array s p n; m < n \<rbrakk> \<Longrightarrow>
   the_array (heap_w32_update (\<lambda>h q. if q = p +\<^sub>p int m then x else f h q) s) p n =
   (the_array (heap_w32_update f s) p n)[m := x]"
  by (auto simp: is_array_def array_loc_valid_def the_array_elem
           intro: nth_equalityI)


lemma multiset_of_cycle:
  (* Courtesy of Dave G *)
  "\<lbrakk> i < length ls; j < length ls; k < length ls; i = k \<Longrightarrow> ls ! i = ls ! j \<rbrakk> \<Longrightarrow>
   mset (ls[i := (ls ! j), j := ls ! k, k := ls ! i]) = mset ls"
  apply (subst (2) mset_swap[symmetric, where i = j and j = i], assumption+)
  apply (subst (2) mset_swap[symmetric, where i = j and j = k], simp+)
  apply (clarsimp simp: nth_list_update)
  apply (metis list_update_overwrite list_update_swap)
  done


(* Defining sanity of program, i.e. that only the array can change,
   and some related lemmas *)

definition unmodified_outside_range ::
             "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "unmodified_outside_range s s' a n \<equiv>
   (\<forall>p. (p < a \<or> (array_not_at_mem_end a n \<and> p \<ge> a +\<^sub>p int n)) \<longrightarrow>
        (is_valid_w32 s' p = is_valid_w32 s p \<and> heap_w32 s' p = heap_w32 s p))"

lemma unmodified_outside_range_refl [simp]:
  "unmodified_outside_range s s a n"
  by (simp add: unmodified_outside_range_def)

lemma unmodified_outside_range_trans:
  "\<lbrakk> unmodified_outside_range s1 s2 a n; unmodified_outside_range s2 s3 a n \<rbrakk>
   \<Longrightarrow> unmodified_outside_range s1 s3 a n"
  by (simp add: unmodified_outside_range_def)

lemma unmodified_outside_empty_range:
  "unmodified_outside_range s s' p 0
   \<Longrightarrow> \<forall>p. (is_valid_w32 s' p = is_valid_w32 s p \<and>
            heap_w32 s' p = heap_w32 s p)"
  apply (clarsimp simp: unmodified_outside_range_def empty_array_not_at_mem_end)
  apply (case_tac "pa < p", simp+)
  done

lemma unmodified_outside_empty_range2:
  "\<lbrakk> unmodified_outside_range s s' p 0; array_loc_valid a n \<rbrakk>
   \<Longrightarrow> unmodified_outside_range s s' a n"
  apply (clarsimp simp: unmodified_outside_range_def empty_array_not_at_mem_end)
  apply (case_tac "pa < p", simp+)
  done

lemma unmodified_outside_subrange1:
  "\<lbrakk> array_loc_valid a n; unmodified_outside_range s s' a m; m \<le> n \<rbrakk>
   \<Longrightarrow> unmodified_outside_range s s' a n"
  apply (unfold unmodified_outside_range_def)
  apply clarsimp
  apply (subgoal_tac "array_not_at_mem_end a m \<and> a +\<^sub>p int m \<le> p", simp)
  apply (simp add: array_not_at_mem_end_def)
  apply (rule_tac y = "a +\<^sub>p int n" in order_trans)
   apply (simp add: array_loc_mono array_not_at_mem_end_def)
  apply assumption
  done

lemma unmodified_outside_subrange2:
  "\<lbrakk> array_loc_valid a n;
     unmodified_outside_range s s' (a +\<^sub>p int m) (n - m); m \<le> n \<rbrakk>
   \<Longrightarrow> unmodified_outside_range s s' a n"
  apply (case_tac "m = n", simp)
   apply (rule_tac p = "a +\<^sub>p int n" in unmodified_outside_empty_range2, assumption+)
  apply (unfold unmodified_outside_range_def)
  apply clarsimp
  apply (simp add: ptr_add_assoc[symmetric])
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac z = "a +\<^sub>p int m" in order_less_le_trans)
    apply (simp add: array_no_wrap)
   apply simp
  apply (auto simp: array_not_at_mem_end_def unat_linear_over_array_loc2)
  done


(* Sanity in terms of arrays not changing *)

lemma is_still_array:
  "\<lbrakk> unmodified_outside_range s s' a n;
     (array_not_at_mem_end a' n' \<and> a' +\<^sub>p int n' \<le> a) \<or>
     (array_not_at_mem_end a n \<and> a +\<^sub>p int n \<le> a') \<or> n = 0;
     is_array s a' n' \<rbrakk> \<Longrightarrow> is_array s' a' n'"
  apply (clarsimp simp: unmodified_outside_range_def is_array_def
                        array_all_elems_valid)
  apply (drule_tac x = "m" in spec, clarsimp)
  apply (drule_tac R = "is_valid_w32 s' (a' +\<^sub>p int m)" in disjE, simp_all)
   apply clarsimp
   apply (subgoal_tac "a' +\<^sub>p int m < a", simp)
   apply (rule_tac y = "a' +\<^sub>p int n'" in less_le_trans)
    apply (rule array_loc_strict_mono, assumption+)
  apply (drule_tac R = "is_valid_w32 s' (a' +\<^sub>p int m)" in disjE, simp_all)
   apply clarsimp
   apply (subgoal_tac "a +\<^sub>p int n \<le> a' +\<^sub>p int m", simp)
   apply (erule_tac y = "a'" in order_trans)
   apply (rule_tac n = "n'" in array_no_wrap, assumption+)
  apply (case_tac "a' +\<^sub>p int m < a", simp)
  apply (simp add: empty_array_not_at_mem_end)
  done

lemma the_same_array:
  "\<lbrakk> unmodified_outside_range s s' a n; array_loc_valid a' n';
     (array_not_at_mem_end a' n' \<and> a' +\<^sub>p int n' \<le> a) \<or>
     (array_not_at_mem_end a n \<and> a' \<ge> a +\<^sub>p int n) \<or> n = 0 \<rbrakk> \<Longrightarrow>
   the_array s' a' n' = the_array s a' n'"
  apply (clarsimp simp: unmodified_outside_range_def the_arrays_equal)
  apply (drule_tac R = "heap_w32 s' (a' +\<^sub>p int m) = heap_w32 s (a' +\<^sub>p int m)"
                in disjE)
    apply simp_all
   apply clarsimp
   apply (subgoal_tac "a' +\<^sub>p int m < a", simp)
   apply (rule_tac y = "a' +\<^sub>p int n'" in less_le_trans)
    apply (rule array_loc_strict_mono, assumption+)
  apply (drule_tac R = "heap_w32 s' (a' +\<^sub>p int m) = heap_w32 s (a' +\<^sub>p int m)"
                in disjE)
    apply simp_all
   apply (subgoal_tac "a +\<^sub>p int n \<le> a' +\<^sub>p int m", simp)
   apply clarsimp
   apply (erule_tac y = "a'" in order_trans)
   apply (rule_tac n = "n'" in array_no_wrap, assumption+)
  apply (case_tac "a' +\<^sub>p int m < a", simp)
  apply (simp add: empty_array_not_at_mem_end)
  done


(*
 * Proof of partition function!
 *)

definition partitioned
where
  "partitioned s a n pivot_idx \<equiv>
   (\<forall>i. i < n \<longrightarrow> (i < pivot_idx \<longleftrightarrow> heap_w32 s (a +\<^sub>p int i) < heap_w32 s (a +\<^sub>p int pivot_idx)))"

lemma partition_correct:
  "\<forall>s0. \<lbrace> \<lambda>s. is_array s a (unat n) \<and> n > 0 \<and> s = s0 \<rbrace>
        partition' a n
        \<lbrace> \<lambda>r s. is_array s a (unat n) \<and>
                mset (the_array s a (unat n)) = mset (the_array s0 a (unat n)) \<and>
                r < n \<and> partitioned s a (unat n) (unat r) \<and>
                unmodified_outside_range s0 s a (unat n) \<rbrace>!"
  apply clarsimp
  apply (unfold partition'_def)
  apply (subst whileLoop_add_inv [where
         I = "\<lambda>(i, pivot_idx) s. is_array s a (unat n) \<and>
                                 mset (the_array s a (unat n)) =
                                 mset (the_array s0 a (unat n)) \<and>
                                 i \<le> n \<and> pivot_idx < i \<and>
                                 partitioned s a (unat i) (unat pivot_idx) \<and>
                                 unmodified_outside_range s0 s a (unat n)" and
         M = "\<lambda>((i, pivot_idx), s). n - i"])

  apply wp
     apply clarsimp
     apply (intro conjI impI)
                 defer
                apply unat_arith
                apply unat_arith
               defer defer
              apply (erule_tac n = "n" in array_valid_elem2, unat_arith)
              apply (rule_tac n = "n" in array_valid_elem2, assumption+)
             apply (erule_tac n = "n" in array_valid_elem2, unat_arith)
            apply unat_arith
           apply unat_arith
          apply (unfold partitioned_def)
          apply clarsimp
          apply (case_tac "i = unat aa")
           apply (simp add: uint_nat, unat_arith)
          apply (subgoal_tac "i < unat aa", simp)
          apply unat_arith
         apply (rule_tac n = "n" in array_valid_elem2, assumption+)
        apply (erule_tac n = "n" in array_valid_elem2, unat_arith)
       apply wp
       apply clarsimp
       apply (intro conjI impI)
        apply unat_arith
       apply unat_arith
      apply clarsimp
     apply clarsimp
     apply unat_arith
    defer
    apply (clarsimp simp: is_array_def array_loc_valid_def uint_nat)
    apply (intro conjI impI allI)
              apply simp
             apply (simp add: CTypesDefs.ptr_add_def)
            apply (simp add: CTypesDefs.ptr_add_def )
           apply (simp add: CTypesDefs.ptr_add_def)
          apply unat_arith
         apply (simp add: CTypesDefs.ptr_add_def)
        apply (subst (asm) (2) ptr_offsets_eq)
          apply (simp, unat_arith)
         apply (simp, unat_arith)
        apply (simp, unat_arith)
       apply (subst (asm) ptr_offsets_eq, simp, unat_arith, simp, unat_arith)+
       apply simp
      apply (subst (asm) (3) ptr_offsets_eq)
        apply (simp, unat_arith)
       apply (simp, unat_arith)
      apply (subst (asm) ptr_offsets_eq, simp, unat_arith, simp, unat_arith)+
      apply clarsimp
      apply (drule_tac x = "unat (b + 1)" in spec)
      apply (subgoal_tac "unat (b + 1) < unat aa")
       apply clarsimp
       apply (subgoal_tac "\<not> unat (b + 1) < unat b")
        apply (subgoal_tac "\<not> unat aa < unat (b + 1)", simp)
        apply simp
       apply unat_arith
      apply unat_arith
     apply (subst (asm) (4) ptr_offsets_eq)
       apply (simp, unat_arith)
      apply (simp, unat_arith)
     apply simp
    apply (subst (asm) ptr_offsets_eq, simp, unat_arith, simp, unat_arith)+
    apply clarsimp
    apply (drule_tac x = "i" in spec)
    apply (subgoal_tac "i < unat aa")
     apply clarsimp
     apply (subgoal_tac "(i < unat b) = (i < unat (b + 1))", simp)
     apply unat_arith
    apply unat_arith
   defer
   apply (simp add: o_def)
   apply (subst uint_nat, subst the_updated_array, assumption, unat_arith)+
   apply (clarsimp simp: is_array_def array_loc_valid_def)
   apply (intro conjI impI)
    apply (subst (asm) ptr_offsets_eq2, simp, unat_arith, simp, unat_arith)
    apply simp
   apply (simp only: uint_nat)
   apply (subst the_array_elem[symmetric, where n = "unat n"], unat_arith)+
   apply (subst multiset_of_cycle)
       apply (simp, unat_arith)
      apply (simp, unat_arith)
     apply (simp, unat_arith)
    apply simp+
  apply (clarsimp simp: is_array_def unmodified_outside_range_def)
  apply (intro conjI impI)
           apply (subst (asm) ptr_offsets_eq2)
             apply simp+
         apply (subgoal_tac "a \<le> a +\<^sub>p uint b", simp)
         apply (rule_tac n = "n" in array_no_wrap2, simp, unat_arith)
        apply clarsimp
        apply (subgoal_tac "a +\<^sub>p uint b < a +\<^sub>p uint n", simp add: uint_nat)
        apply (erule_tac n = "n" in array_loc_strict_mono2, unat_arith)
       apply (subgoal_tac "a \<le> a +\<^sub>p uint (b + 1)", simp)
       apply (erule_tac n = "n" in array_no_wrap2, unat_arith)
      apply clarsimp
      apply (subgoal_tac "a +\<^sub>p uint aa < a +\<^sub>p uint n", simp add: uint_nat)
      apply (rule_tac n = "n" in array_loc_strict_mono2, assumption+)
     apply (subgoal_tac "a \<le> a +\<^sub>p uint aa", simp)
     apply (rule_tac n = "n" in array_no_wrap2, assumption+)
    apply clarsimp
    apply (subgoal_tac "a +\<^sub>p uint aa < a +\<^sub>p uint n", simp add: uint_nat)
    apply (rule_tac n = "n" in array_loc_strict_mono2, assumption+)
   apply (subgoal_tac "a \<le> a +\<^sub>p uint (b + 1)", simp)
   apply (erule_tac n = "n" in array_no_wrap2, unat_arith)
  apply clarsimp
  apply (subgoal_tac "a +\<^sub>p uint (b + 1) < a +\<^sub>p uint n", simp add: uint_nat)
  apply (erule_tac n = "n" in array_loc_strict_mono2, unat_arith)
  done


(* Induction rule used for quicksort proof *)
lemma word_strong_induct[case_names Ind]:
  "(\<And>n. (\<forall>k < n. P k) \<Longrightarrow> P n) \<Longrightarrow> P (m::addr)"
  by (rule less_induct, blast)


(* Some extra Hoare logic rules *)

lemma when_True:
  "P \<Longrightarrow> when P A = A"
  by monad_eq

lemma when_False:
  "\<not> P \<Longrightarrow> when P A = return ()"
  by monad_eq

lemma hoare_save_pre_state:
  "(\<And>s'. P s' \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> s = s' \<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def)

lemma validNF_save_pre_state:
  "(\<And>s'. P s' \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> s = s' \<rbrace> f \<lbrace>Q\<rbrace>!) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"
  by (auto simp: validNF_def valid_def no_fail_def)


lemma is_array_after_changing_left:
  "\<lbrakk> m \<le> n; is_array s1 a n; is_array s2 a m;
     unmodified_outside_range s1 s2 a m \<rbrakk>
   \<Longrightarrow> is_array s2 a n"
  apply (case_tac "m = n", simp)
  apply (frule_tac m = "m" in subarray_not_at_mem_end2, simp)
  apply (erule_tac m = "m" in concat_is_array)
    apply (auto simp: is_still_array subarray2_is_array)
  done

lemma is_array_after_changing_right:
  "\<lbrakk> m \<le> n; is_array s1 a n; is_array s2 (a +\<^sub>p int m) (n - m);
     unmodified_outside_range s1 s2 (a +\<^sub>p int m) (n - m) \<rbrakk>
   \<Longrightarrow> is_array s2 a n"
  apply (case_tac "m = n")
   apply (simp add: is_array_def array_all_elems_valid unmodified_outside_empty_range)
  apply (frule_tac m = "m" in subarray_not_at_mem_end2, simp)
  apply (rule_tac m = "m" in concat_is_array)
     apply (rule_tac s = "s1" and a = "a +\<^sub>p int m" and n = "n - m" in is_still_array)
       apply simp+
     apply (rule_tac n = "n" in subarray1_is_array)
      apply simp+
  done


(*
 * There is an issue later on with using "subst" substitutions on expressions
 * involving certain variables, so we have to use "rule_tac" with rules like
 * the following.
 *)
lemma multiset_of_concat_array:
  "\<lbrakk> m \<le> n; mset (the_array s a m) = mset (the_array s' a m);
     mset (the_array s (a +\<^sub>p int m) (n - m)) = mset (the_array s' (a +\<^sub>p int m) (n - m)) \<rbrakk>
   \<Longrightarrow> mset (the_array s a n) = mset (the_array s' a n)"
  by (simp add: the_array_concat2)

lemma multiset_same_after_shuffling_left:
  "\<lbrakk> m \<le> n; array_loc_valid a n;
     mset (the_array s1 a m) = mset (the_array s2 a m);
     unmodified_outside_range s1 s2 a m \<rbrakk>
   \<Longrightarrow> mset (the_array s1 a n) = mset (the_array s2 a n)"
  apply (case_tac "m = n", simp)
  apply (frule_tac m = "m" in subarray_not_at_mem_end1, simp)
  apply (rule_tac m = "m" in multiset_of_concat_array, assumption+)
  apply (subgoal_tac "the_array s2 (a +\<^sub>p int m) (n - m) =
                      the_array s1 (a +\<^sub>p int m) (n - m)", simp)
  apply (erule_tac a = "a" and n = "m" in the_same_array)
   apply (clarsimp simp: is_array_def array_loc_valid_def
                         unat_linear_over_array_loc2, unat_arith)
  apply simp
  done

lemma multiset_same_after_shuffling_right:
  "\<lbrakk> m \<le> n; array_loc_valid a n;
     mset (the_array s1 (a +\<^sub>p int m) (n - m)) =
     mset (the_array s2 (a +\<^sub>p int m) (n - m));
     unmodified_outside_range s1 s2 (a +\<^sub>p int m) (n - m) \<rbrakk>
   \<Longrightarrow> mset (the_array s1 a n) = mset (the_array s2 a n)"
  apply (rule_tac m = "m" in multiset_of_concat_array)
    apply assumption
   apply (subgoal_tac "the_array s2 a m = the_array s1 a m", simp)
   apply (case_tac "m = n")
    apply (simp add: unmodified_outside_empty_range the_arrays_equal)
   apply (frule_tac m = "m" in subarray_not_at_mem_end1, simp)
   apply (rule_tac a = "a +\<^sub>p int m" and n = "n - m" in the_same_array)
    apply (auto simp: array_not_at_mem_end_def array_loc_valid_def)
  done


(* Preparing for lemmas about partitioned-ness being preserved *)

lemma old_array_elem:
  "\<lbrakk> mset (the_array s a n) =
     mset (the_array s0 a n); i < n \<rbrakk>
   \<Longrightarrow> \<exists>j < n. heap_w32 s (a +\<^sub>p int i) = heap_w32 s0 (a +\<^sub>p int j)"
  apply (drule mset_eq_setD)
  apply (subgoal_tac "heap_w32 s (a +\<^sub>p int i) \<in> set (the_array s a n)")
   apply simp
   apply (frule nth_the_index)
   apply (rule_tac x = "the_index (the_array s0 a n) (heap_w32 s (a +\<^sub>p int i))"
          in exI)
   apply (rule conjI)
    apply (subst (4) the_array_length[symmetric, where s = "s0" and a = "a"])
    apply (erule the_index_bounded)
   apply (subst (asm) the_array_elem)
    apply (subst (4) the_array_length[symmetric, where s = "s0" and a = "a"])
    apply (erule the_index_bounded)
   apply simp
  apply (subst the_array_elem[symmetric, where n = "n"], assumption)
  apply (rule nth_mem, simp)
  done

lemma old_array_elem2:
  "\<lbrakk> mset (the_array s (a +\<^sub>p int k) (n - k)) =
     mset (the_array s0 (a +\<^sub>p int k) (n - k)); k + i < n \<rbrakk>
   \<Longrightarrow> \<exists>j < n. j \<ge> k \<and> heap_w32 s (a +\<^sub>p int (k + i)) = heap_w32 s0 (a +\<^sub>p int j)"
  apply (drule_tac i = "i" in old_array_elem, simp)
  apply clarsimp
  apply (rule_tac x = "k + j" in exI)
  apply simp
  done

lemma partitioned_after_shuffling_left:
  "\<lbrakk> is_array s0 a (unat n); pivot_idx < n;
     partitioned s0 a (unat n) (unat pivot_idx);
     mset (the_array s a (unat pivot_idx)) =
     mset (the_array s0 a (unat pivot_idx));
     unmodified_outside_range s0 s a (unat pivot_idx) \<rbrakk>
   \<Longrightarrow> partitioned s a (unat n) (unat pivot_idx)"
  apply (clarsimp simp: partitioned_def unmodified_outside_range_def)
  apply (subgoal_tac "heap_w32 s (a +\<^sub>p uint pivot_idx) =
                      heap_w32 s0 (a +\<^sub>p uint pivot_idx)", simp add: uint_nat)
   apply (subgoal_tac "array_not_at_mem_end a (unat pivot_idx)")
    apply (case_tac "i < unat pivot_idx", clarsimp)
     apply (subgoal_tac "\<exists>j. (j < unat pivot_idx \<and>
                              heap_w32 s (a +\<^sub>p int i) = heap_w32 s0 (a +\<^sub>p int j))")
      apply clarsimp
      apply (drule_tac x = "j" in spec)
      apply (subgoal_tac "j < unat n")
       apply (clarsimp simp: uint_nat)
      apply unat_arith
     apply (erule old_array_elem, simp)
    apply (drule_tac x = "a +\<^sub>p int i" in spec)
    apply (subgoal_tac "a +\<^sub>p int (unat pivot_idx) \<le> a +\<^sub>p int i")
     apply simp
    apply (rule array_loc_mono)
     apply (rule_tac s = "s0" and n = "unat n" in subarray_not_at_mem_end2,
            assumption+)
    apply unat_arith
   apply (erule_tac s = "s0" and n = "unat n" in subarray_not_at_mem_end2,
          unat_arith)
  apply (drule_tac x = "a +\<^sub>p uint pivot_idx" in spec)
  apply (subgoal_tac "array_not_at_mem_end a (unat pivot_idx)")
   apply (simp add: uint_nat)
  apply (erule_tac s = "s0" and n = "unat n" in subarray_not_at_mem_end2,
         unat_arith)
  done

lemma partitioned_after_shuffling_right:
  "\<lbrakk> is_array s0 a (unat n); pivot_idx < n;
     partitioned s0 a (unat n) (unat pivot_idx);
     mset (the_array s (a +\<^sub>p int (Suc (unat pivot_idx)))
                       (unat n - Suc (unat pivot_idx))) =
     mset (the_array s0 (a +\<^sub>p int (Suc (unat pivot_idx)))
                        (unat n - Suc (unat pivot_idx)));
     unmodified_outside_range s0 s (a +\<^sub>p int (Suc (unat pivot_idx)))
                                   (unat n - unat pivot_idx - 1) \<rbrakk>
   \<Longrightarrow> partitioned s a (unat n) (unat pivot_idx)"
  apply (unfold partitioned_def)
  apply (case_tac "unat n = Suc (unat pivot_idx)")
   apply (simp add: unmodified_outside_empty_range)
  apply (subgoal_tac "Suc (unat pivot_idx) < unat n")
   prefer 2
   apply unat_arith
  apply (subgoal_tac "array_not_at_mem_end a (Suc (unat pivot_idx))")
   prefer 2
   apply (rule_tac s = "s0" and n = "unat n" in subarray_not_at_mem_end2)
    apply assumption+
  apply (unfold unmodified_outside_range_def, clarify)
  apply (frule_tac x = "a +\<^sub>p int (unat pivot_idx)" in spec)
  apply (subgoal_tac "a +\<^sub>p int (unat pivot_idx) < a +\<^sub>p int (Suc (unat pivot_idx))")
   prefer 2
   apply (erule array_loc_strict_mono, simp)
  apply (case_tac "i \<le> unat pivot_idx")
   apply (frule_tac x = "a +\<^sub>p int i" in spec)
   apply (subgoal_tac "a +\<^sub>p int i < a +\<^sub>p int (Suc (unat pivot_idx))")
     apply (simp add: uint_nat)
    apply (erule array_loc_strict_mono, simp)
  apply (subgoal_tac "\<not> i < unat pivot_idx")
   prefer 2
   apply unat_arith
  apply (drule_tac i = "i - Suc (unat pivot_idx)" in old_array_elem2)
   apply unat_arith
  apply clarify
  apply (frule_tac x = "j" in spec)
  apply (subgoal_tac "\<not> j < unat pivot_idx")
   apply (subgoal_tac "a +\<^sub>p 1 +\<^sub>p int (unat pivot_idx) +\<^sub>p
                       int (i - Suc (unat pivot_idx)) = a +\<^sub>p int i")
    apply simp
   apply (subst of_nat_diff, unat_arith)
   apply (subst ptr_add_assoc[symmetric])+
   apply simp
  apply unat_arith
  done


(*
 * The basic idea of quicksort: if the array is partitioned and
 * both halves are sorted then the array is sorted.
 *)

lemma partitioned_array_sorted:
  "\<lbrakk> m < n; sorted (the_array s a m);
     sorted (the_array s (a +\<^sub>p int (Suc m)) (n - Suc m));
     partitioned s a n m \<rbrakk> \<Longrightarrow>
   sorted (the_array s a n)"
  apply (subst the_array_concat2[where m = "m"], simp)
  apply (subst sorted_append, simp)
  apply (rule conjI)
   apply (subst the_array_concat2[where m = "1"], simp+)
   apply (simp add: partitioned_def)
   apply (subst all_set_conv_all_nth)
   apply (clarsimp simp: the_array_elem)
   apply (drule_tac x = "m + i + 1" in spec)
   apply (subgoal_tac "m + i + 1 < n")
    apply clarsimp
    apply unat_arith
   apply unat_arith
  apply (subst all_set_conv_all_nth)
  apply (clarsimp simp: the_array_elem partitioned_def)
  apply (frule_tac x = "i" in spec)
  apply simp
  apply (subgoal_tac "x \<ge> heap_w32 s (a +\<^sub>p int m)")
   apply simp
  apply (frule nth_the_index)
  apply (subst (asm) the_array_elem)
  apply (frule the_index_bounded, simp)
  apply (subgoal_tac "m + the_index (the_array s (a +\<^sub>p int m) (n - m)) x < n")
   apply (frule_tac x = "m + the_index (the_array s (a +\<^sub>p int m) (n - m)) x"
          in spec)
   apply simp
  apply (subgoal_tac "the_index (the_array s (a +\<^sub>p int m) (n - m)) x < n - m")
   apply simp
  apply (frule the_index_bounded, simp)
  done


(* Some more trivial lemmas *)

lemma array_index_Suc:
  "a +\<^sub>p uint m +\<^sub>p 1 = a +\<^sub>p int (Suc (unat m))"
  by (simp add: uint_nat)

lemma array_loc_le_Suc:
  "array_not_at_mem_end a (Suc (unat m)) \<Longrightarrow> a +\<^sub>p int (unat m) \<le> a +\<^sub>p 1 +\<^sub>p uint m"
  apply (subst ptr_add_commute)
  apply (subst array_index_Suc)
  apply (rule array_loc_mono, simp+)
  done

lemma unat_sub_sub1 [simp]:
  "(m::addr) < n \<Longrightarrow> unat (n - m - 1) = unat n - unat m - 1"
  by unat_arith

lemma unat_inc:
  "(m::addr) < n \<Longrightarrow> unat (m + 1) = Suc (unat m)"
  by unat_arith


lemma old_quicksort_correct:
  shows "\<lbrace> \<lambda>s. is_array s a (unat n) \<and> s = s0 \<and> unat n < m \<rbrace>
         quicksort' m a n
         \<lbrace> \<lambda>r s. is_array s a (unat n) \<and>
                 mset (the_array s a (unat n)) =
                 mset (the_array s0 a (unat n)) \<and>
                 sorted (the_array s a (unat n)) \<and>
                 unmodified_outside_range s0 s a (unat n) \<rbrace>!"
   ( is "\<lbrace> ?pre a n s0 m \<rbrace> quicksort' m a n \<lbrace> ?post a n s0 \<rbrace>!" )
  oops

(* FIXME: move *)
(* This puts our {partition,quicksort}_correct lemmas into a form that
   wp can use. *)
lemma make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (auto simp add: valid_def validNF_def no_fail_def split: prod.splits)


(*
 * Proof of recursive quicksort function!
 *)

lemma quicksort_correct:
  shows "\<forall>a m s0. \<lbrace> \<lambda>s. is_array s a (unat n) \<and> s = s0 \<and> unat n < m \<rbrace>
         quicksort' m a n
         \<lbrace> \<lambda>r s. is_array s a (unat n) \<and>
                 mset (the_array s a (unat n)) =
                 mset (the_array s0 a (unat n)) \<and>
                 sorted (the_array s a (unat n)) \<and>
                 unmodified_outside_range s0 s a (unat n) \<rbrace>!"
   ( is "\<forall>a m s0. \<lbrace> ?pre a n s0 m \<rbrace> quicksort' m a n \<lbrace> ?post a n s0 \<rbrace>!" )

proof (induct n rule: word_strong_induct)
  fix a m s0

next
  fix a n m s0
  assume quicksort_ind_hyp:
    "\<forall>k < n. \<forall>a m s0. \<lbrace> ?pre a k s0 m \<rbrace> quicksort' m a k \<lbrace> ?post a k s0 \<rbrace>!"

  have quicksort_ind_hyp':
    "\<And>k a m. \<forall>s0. \<lbrace> \<lambda>s. ?pre a k s0 m s \<and> k < n \<rbrace> quicksort' m a k \<lbrace> ?post a k s0 \<rbrace>!"
    apply clarsimp
    apply (rule validNF_assume_pre)
    apply (rule validNF_chain)
      apply (rule quicksort_ind_hyp [rule_format])
      apply auto
    done

  show "\<forall>a m s0. \<lbrace> ?pre a n s0 m \<rbrace> quicksort' m a n \<lbrace> ?post a n s0 \<rbrace>!"
    apply clarsimp
    apply (subst quicksort'.simps)
    apply (unfold when_def)
    apply (wp quicksort_ind_hyp' [THEN make_schematic_post]
              partition_correct  [THEN make_schematic_post])
    apply clarsimp
    apply safe
              apply unat_arith
             apply (erule subarray1_is_array, unat_arith)
            apply unat_arith
           apply (case_tac "unat n = Suc (unat rv)", simp add: empty_array_is_array)
           (* Add a few useful facts into the assumption set *)
           apply (frule_tac s = "s'" and m = "unat rv" in subarray_not_at_mem_end2, unat_arith)
           apply (frule_tac s = "s'" and m = "Suc (unat rv)" in subarray_not_at_mem_end2, unat_arith)
           apply (frule_tac s = "s'" and m = "unat rv" in subarray1_is_array, unat_arith)
           apply (frule_tac s = "s'" and m = "unat rv" in subarray2_is_array, unat_arith, simp)
           apply (frule_tac s = "s'" and m = "Suc (unat rv)" in subarray1_is_array, unat_arith)
           apply (frule_tac s = "s'" and m = "Suc (unat rv)" in subarray2_is_array,
                  unat_arith, simp)
           (* ...and back to the proof *)
           apply (erule is_still_array)
            apply (rule disjI2, rule disjI1)
            apply (simp add: array_loc_le_Suc)
           apply (simp add: uint_nat)
          apply unat_arith
         apply unat_arith
        apply (rule_tac ?s1.0 = "s'a" and m = "Suc (unat rv)"
                     in is_array_after_changing_right)
           apply unat_arith
          apply (rule_tac ?s1.0 = "s'" and m = "unat rv"
                       in is_array_after_changing_left)
             apply unat_arith
            apply assumption+
         apply (simp add: uint_nat)+
       apply (subgoal_tac "mset (the_array s'b a (unat n)) =
                           mset (the_array s'a a (unat n))")
        apply (subgoal_tac "mset (the_array s'a a (unat n)) =
                            mset (the_array s' a (unat n))", simp)
        apply (rule_tac m = "unat rv" in multiset_same_after_shuffling_left)
           apply unat_arith
          apply (simp add: is_array_def)
         apply assumption
        apply (simp add: unmodified_outside_range_def)
       apply (rule_tac m = "Suc (unat rv)" in multiset_same_after_shuffling_right)
          apply unat_arith
         apply (simp add: is_array_def)
        apply simp
       apply (simp add: unmodified_outside_range_def)
      apply (rule_tac m = "unat rv" in partitioned_array_sorted)
         apply unat_arith
        apply (subgoal_tac "the_array s'b a (unat rv) = the_array s'a a (unat rv)", simp)
        apply (case_tac "Suc (unat rv) = unat n")
         apply (simp add: unmodified_outside_empty_range the_arrays_equal)
        apply (erule_tac a = "a +\<^sub>p 1 +\<^sub>p uint rv" and n = "unat n - Suc (unat rv)"
                     in the_same_array)
         apply (simp add: is_array_def)
        apply (rule disjI1, rule conjI)
         apply (erule subarray_not_at_mem_end2, unat_arith)
        apply (rule array_loc_le_Suc)
        apply (erule subarray_not_at_mem_end2, unat_arith)
       apply (simp add: uint_nat)
      apply (rule_tac ?s0.0 = "s'a" in partitioned_after_shuffling_right)
          apply (rule_tac ?s1.0 = "s'" and m = "unat rv" in is_array_after_changing_left)
             apply unat_arith
            apply assumption+
        apply (rule_tac ?s0.0 = "s'" in partitioned_after_shuffling_left, assumption+)
       apply (simp add: uint_nat)+
     apply (erule unmodified_outside_range_trans)
     apply (rule_tac ?s2.0 = "s'a" in unmodified_outside_range_trans)
      apply (rule_tac m = "unat rv" in unmodified_outside_subrange1)
        apply (simp add: is_array_def)
       apply assumption
      apply unat_arith
     apply (rule_tac m = "Suc (unat rv)" in unmodified_outside_subrange2)
       apply (simp add: is_array_def)
      apply (simp add: uint_nat)
     apply unat_arith
    apply (case_tac "n = 1", simp)
    apply (subgoal_tac "n = 0", simp, unat_arith)
    done

qed

end

end

