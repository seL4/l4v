(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory ArrayAssertion

imports
  "$L4V_ARCH/ArchArraysMemInstance"
  "StructSupport"

begin

lemma array_tag_n_eq:
  "(array_tag_n n :: ('a :: c_type['b :: finite]) field_desc typ_desc) =
  TypDesc (TypAggregate
    (map (\<lambda>n. DTPair (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. index x n)
            (\<lambda>x f. Arrays.update f n x)) (replicate n CHR ''1'')) [0..<n]))
  (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b :: finite set)))"
  apply (induct n)
   apply (simp add: typ_info_array array_tag_def eval_nat_numeral array_tag_n.simps empty_typ_info_def)
   apply (simp add: typ_info_array array_tag_def eval_nat_numeral array_tag_n.simps empty_typ_info_def)
   apply (simp add: ti_typ_combine_def Let_def)
   done

lemma typ_info_array':
  "typ_info_t TYPE ('a :: c_type['b :: finite]) =
  TypDesc (TypAggregate
    (map (\<lambda>n. DTPair (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. index x n)
            (\<lambda>x f. Arrays.update f n x)) (replicate n CHR ''1'')) [0..<(card (UNIV :: 'b :: finite set))]))
  (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b :: finite set)))"
  by (simp add: typ_info_array array_tag_def array_tag_n_eq)

definition
  "uinfo_array_tag_n_m (v :: 'a itself) n m = TypDesc
    (TypAggregate (map (\<lambda>i. DTPair (typ_uinfo_t TYPE('a)) (replicate i CHR ''1'')) [0 ..< n]))
    (typ_name (typ_uinfo_t TYPE('a :: c_type)) @ ''_array_'' @ nat_to_bin_string m)"

lemma map_td_list_map:
  "map_td_list f = map (map_td_pair f)"
  by (rule ext, rename_tac x) (induct_tac x, simp_all)

lemma uinfo_array_tag_n_m_eq:
  "n \<le> CARD('b)
    \<Longrightarrow> export_uinfo (array_tag_n n :: (('a :: wf_type)['b :: finite]) field_desc typ_desc)
        = uinfo_array_tag_n_m TYPE ('a) n (CARD('b))"
  apply (clarsimp simp: uinfo_array_tag_n_m_def array_tag_n_eq map_td_list_map
                        o_def adjust_ti_def map_td_map typ_uinfo_t_def export_uinfo_def)
  apply (fastforce intro: map_td_extI simp: field_norm_blah)
  done

lemma typ_uinfo_array_tag_n_m_eq:
  "typ_uinfo_t TYPE (('a :: wf_type)['b :: finite])
        = uinfo_array_tag_n_m TYPE ('a) (CARD('b)) (CARD('b))"
  by (simp add: typ_uinfo_t_def typ_info_array array_tag_def uinfo_array_tag_n_m_eq)

text \<open>Alternative to h_t_valid for arrays. This allows reasoning
about arrays of variable width.\<close>
definition h_t_array_valid :: "heap_typ_desc \<Rightarrow> ('a :: c_type) ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "h_t_array_valid htd ptr n = valid_footprint htd (ptr_val ptr) (uinfo_array_tag_n_m TYPE ('a) n n)"

text \<open>Assertion that pointer p is within an array that continues for at least n more elements.\<close>
definition
  "array_assertion (p :: ('a :: c_type) ptr) n htd
    = (\<exists>q i j. h_t_array_valid htd q j
        \<and> p = CTypesDefs.ptr_add q (int i) \<and> i < j \<and> i + n \<le> j)"

lemma array_assertion_shrink_right:
  "array_assertion p n htd \<Longrightarrow> n' \<le> n \<Longrightarrow> array_assertion p n' htd"
  by (fastforce simp: array_assertion_def)

lemma array_assertion_shrink_leftD:
  "array_assertion p n htd \<Longrightarrow> j < n \<Longrightarrow> array_assertion (CTypesDefs.ptr_add p (int j)) (n - j) htd"
  apply (clarsimp simp: array_assertion_def)
  apply (rule exI, rule_tac x="i + j" in exI, rule exI, erule conjI)
  apply (simp add: CTypesDefs.ptr_add_def field_simps)
  done

lemma array_assertion_shrink_leftI:
  "array_assertion (CTypesDefs.ptr_add p (- (int j))) (n + j) htd
    \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> array_assertion p n htd"
  apply (drule_tac j=j in array_assertion_shrink_leftD, simp)
  apply (simp add: CTypesDefs.ptr_add_def)
  done

lemma h_t_array_valid:
  "h_t_valid htd gd (p :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> h_t_array_valid htd (ptr_coerce p :: 'a ptr) (CARD('b))"
  by (clarsimp simp: h_t_valid_def h_t_array_valid_def typ_uinfo_array_tag_n_m_eq)

lemma array_ptr_valid_array_assertionD:
  "h_t_valid htd gd (p :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> array_assertion (ptr_coerce p :: 'a ptr) (CARD('b)) htd"
  apply (clarsimp simp: array_assertion_def dest!: h_t_array_valid)
  apply (fastforce intro: exI[where x=0])
  done

lemma array_ptr_valid_array_assertionI:
  "h_t_valid htd gd (q :: (('a :: wf_type)['b :: finite]) ptr)
    \<Longrightarrow> q = ptr_coerce p
    \<Longrightarrow> n \<le> CARD('b)
    \<Longrightarrow> array_assertion (p :: 'a ptr) n htd"
  by (auto dest: array_ptr_valid_array_assertionD
           simp: array_assertion_shrink_right)

text \<open>Derived from array_assertion, an appropriate assertion for performing
a pointer addition, or for dereferencing a pointer addition (the strong case).

In either case, there must be an array connecting the two ends of the pointer
transition, with the caveat that the last address can be just out of the array
if the pointer is not dereferenced, thus the strong/weak distinction.

If the pointer doesn't actually move, nothing is learned.
\<close>
definition ptr_add_assertion :: "('a :: c_type) ptr \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> bool" where
  "ptr_add_assertion ptr offs strong htd \<equiv>
    offs = 0 \<or>
    array_assertion (if offs < 0 then CTypesDefs.ptr_add ptr offs else ptr)
                    (if offs < 0 then nat (- offs) else if strong then Suc (nat offs) else nat offs)
                    htd"

lemma ptr_add_assertion_positive:
  "offs \<ge> 0 \<Longrightarrow> ptr_add_assertion ptr offs strong htd
    = (offs = 0 \<or> array_assertion ptr (case strong of True \<Rightarrow> Suc (nat offs)
        | False \<Rightarrow> nat offs) htd)"
  by (simp add: ptr_add_assertion_def)

lemma ptr_add_assertion_negative:
  "offs < 0 \<Longrightarrow> ptr_add_assertion ptr offs strong htd
    = array_assertion (CTypesDefs.ptr_add ptr offs) (nat (- offs)) htd"
  by (simp add: ptr_add_assertion_def)

lemma ptr_add_assertion_uint[simp]:
  "ptr_add_assertion ptr (uint offs) strong htd
    = (offs = 0 \<or> array_assertion ptr
        (case strong of True \<Rightarrow> Suc (unat offs) | False \<Rightarrow> unat offs) htd)"
  by (simp add: ptr_add_assertion_positive uint_0_iff unat_def
         split: bool.split)

text \<open>Ignore char and void pointers. The C standard specifies that arithmetic on
char and void pointers doesn't create any special checks.\<close>

definition ptr_add_assertion' :: "('a :: c_type) ptr \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> bool" where
  "ptr_add_assertion' ptr offs strong htd =
     (typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE(word8)
      \<or> typ_uinfo_t TYPE ('a) = typ_uinfo_t TYPE(unit)
      \<or> ptr_add_assertion ptr offs strong htd)"

(* Useful for clearing away these assumptions. *)
lemma td_diff_from_typ_name:
  "typ_name td \<noteq> typ_name td' \<Longrightarrow> td \<noteq> td'"
  by clarsimp

lemma typ_name_void:
  "typ_name (typ_uinfo_t TYPE(unit)) = ''unit''"
 by (simp add: typ_uinfo_t_def)

lemmas ptr_add_assertion' = ptr_add_assertion'_def td_diff_from_typ_name typ_name_void

text \<open>Mechanism for retyping a range of memory to a non-constant array size.\<close>

definition ptr_arr_retyps :: "nat \<Rightarrow> ('a :: c_type) ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_arr_retyps n p \<equiv>
    htd_update_list (ptr_val p)
        (map (\<lambda>i. list_map (typ_slice_t (uinfo_array_tag_n_m TYPE('a) n n) i))
             [0..<n * size_of TYPE('a)])"

lemma ptr_arr_retyps_to_retyp:
  "n = CARD('b :: finite)
    \<Longrightarrow> ptr_arr_retyps n (p :: ('c :: wf_type) ptr) = ptr_retyp (ptr_coerce p :: ('c['b]) ptr)"
  by (auto simp: ptr_arr_retyps_def ptr_retyp_def typ_slices_def typ_uinfo_array_tag_n_m_eq)

end
