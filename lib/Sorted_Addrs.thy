(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sorted_Addrs
imports
  Word_Lib.WordSetup
  Eisbach_Tools.Eisbach_Methods
begin

(* Proving pspace_distinct' produces quadratically many slow arithmetic proof obligations when
   done directly. If we instead provide a sorted list of addresses of non-overlapping objects,
   pspace_distinct' follows abstractly. Proving that a list of addresses is sorted and
   non-overlapping produces only linearly many proof obligations.

   The local sorted_addrs below defines sorted lists of addresses for non-overlapping objects
   and derives and unfolded version of pspace_distinct'. because pspace_distinct' itself is not
   yet available. See lemma obj_spaced_distinct.

   The locale can be instantiated to the abstract and design levels by providing either obj_bits
   or objBitsKO as a parameter at interpretation.

   In addition to a plain list of object addresses, there are also helper functions for defining
   lists of aligned offsets within a larger region, for instance for CNodes or page tables, and
   for appending these into the global sorted list of objects.

   See proof/infoflow/refine/RISCV64/Example_Valid_StateH.thy for an example of how this is used.
*)


(* Addresses of objects inside CNodes or page tables. p is the start of the encompassing object
   region, sz its size in bits, and `align` the homogeneous alignment (and size) of the smaller
   objects within. These will automatically be sorted and non-overlapping. *)
definition aligned_offsets :: "'a::len word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word list" where
  "aligned_offsets p sz align = [p, p + 2^align .e. p + mask sz]"

locale sorted_addrs =
  fixes bits_of :: "'o \<Rightarrow> nat" (* this is for obj_bits or objBitsKO *)
begin

(* get alignment of an object at specific address *)
definition align_of :: "('a::len word \<rightharpoonup> 'o) \<Rightarrow> 'a word \<Rightarrow> nat" where
  "align_of kh p \<equiv> case kh p of Some obj \<Rightarrow> bits_of obj | None \<Rightarrow> 0"

(* the objects in the list are ordered by address and non-overlapping *)
fun obj_spaced :: "('a::len word \<rightharpoonup> 'o) \<Rightarrow> 'a word list \<Rightarrow> bool" where
  "obj_spaced kh []        = True"
| "obj_spaced kh [p]       = True"
| "obj_spaced kh (p#p'#ps) = (p + mask (align_of kh p) < p' \<and> obj_spaced kh (p'#ps))"

(* pspace_aligned' in a more convenient form. The following is expected to hold when instantiated
   to the design spec level:
   "\<lbrakk> pspace_aligned' s; set addrs = dom (ksPSpace s) \<rbrakk> \<Longrightarrow> obj_aligned (ksPSpace s) addrs" *)
definition obj_aligned :: "('a::len word \<rightharpoonup> 'o) \<Rightarrow> 'a word list \<Rightarrow> bool" where
  "obj_aligned kh addrs \<equiv> \<forall>p \<in> set addrs. is_aligned p (align_of kh p)"

(* all objects in the set have the given alignment *)
definition offsets_align :: "('a::len word \<rightharpoonup> 'o) \<Rightarrow> 'a word set \<Rightarrow> nat \<Rightarrow> bool" where
  "offsets_align kh addrs n \<equiv> \<forall>p \<in> addrs. align_of kh p = n"


(* Lemmas *)

lemma obj_spaced_nth:
  "obj_spaced kh xs = (\<forall>i. Suc i < length xs \<longrightarrow>
                           xs ! i + mask (align_of kh (xs ! i)) < xs ! Suc i)"
  by (induct xs rule: obj_spaced.induct; fastforce simp: nth_Cons split: nat.split)

lemma sorted_imp_obj_spaced:
  "sorted_wrt (\<lambda>p p'. p + mask (align_of kh p) < p') xs \<Longrightarrow> obj_spaced kh xs"
  by (induct xs rule: obj_spaced.induct) auto

lemma obj_spaced_imp_sorted:
  "\<lbrakk> obj_aligned kh addrs; set xs \<subseteq> set addrs; obj_spaced kh xs \<rbrakk> \<Longrightarrow>
   sorted_wrt (\<lambda>p p'. p + mask (align_of kh p) < p') xs"
  apply (induct xs rule: obj_spaced.induct; clarsimp)
  apply (meson aligned_add_mask_lessD basic_trans_rules(19) obj_aligned_def)
  done

lemma obj_spaced_sorted:
  "obj_aligned kh ps \<Longrightarrow> obj_spaced kh ps = sorted_wrt (\<lambda>p p'. p + mask (align_of kh p) < p') ps"
  by (auto intro!: obj_spaced_imp_sorted sorted_imp_obj_spaced)

lemma obj_spaced_append:
  "obj_spaced kh (xs @ ys) =
   (obj_spaced kh xs \<and> obj_spaced kh ys \<and>
    (xs \<noteq> [] \<longrightarrow> ys \<noteq> [] \<longrightarrow> last xs + mask (align_of kh (last xs)) < hd ys))"
  apply (induct xs rule: obj_spaced.induct; simp)
  apply (case_tac ys, auto)
  done

lemma obj_spaced_distinct:
  "\<lbrakk> obj_spaced kh addrs; obj_aligned kh addrs; dom kh = set addrs; kh p = Some ko \<rbrakk> \<Longrightarrow>
   (mask_range p (bits_of ko) - {p}) \<inter> dom kh = {}"
  apply (simp add: obj_spaced_sorted sorted_wrt_iff_nth_less)
  apply (clarsimp simp: obj_aligned_def)
  apply (prop_tac "p \<in> set addrs", fastforce)
  apply (frule (1) bspec)
  apply (simp add: align_of_def)
  apply (rule Int_emptyI)
  apply (rename_tac p')
  apply clarsimp
  apply (drule_tac x=p' in bspec, assumption)
  apply (prop_tac "\<exists>ko'. kh p' = Some ko'", fastforce)
  apply (clarsimp simp: in_set_conv_nth)
  apply (rename_tac i j ko')
  apply (case_tac "i < j"; clarsimp)
   apply (erule allE)+
   apply (erule (1) impE, erule (1) impE)
   apply simp
  apply (clarsimp simp: not_less le_less)
  apply (prop_tac "i \<noteq> j", fastforce)
  apply simp
  apply (erule allE)+
  apply (erule (1) impE, erule (1) impE)
  apply simp
  apply (drule is_aligned_no_overflow_mask)+
  apply fastforce
  done


(* Arrays of small objects: aligned_offsets *)

lemma length_aligned_offsets:
  "is_aligned p sz \<Longrightarrow>
   length (aligned_offsets p sz align) = Suc (unat ((mask sz :: 'a word) div 2 ^ align))"
  for p::"'a::len word"
  unfolding aligned_offsets_def
  apply (subst length_upto_enum_step)
   apply (erule is_aligned_no_overflow_mask)
  apply simp
  done

lemma aligned_offsets_nth:
  "\<lbrakk> is_aligned p sz; n < length (aligned_offsets p sz align) \<rbrakk> \<Longrightarrow>
   aligned_offsets p sz align ! n = p + of_nat n * 2^align"
  apply (simp add: aligned_offsets_def)
  apply (subst upto_enum_step_nth)
    apply (erule is_aligned_no_overflow_mask)
   apply simp
   apply (subst (asm) length_upto_enum_step)
    apply (erule is_aligned_no_overflow_mask)
   apply simp
  apply simp
  done

lemma aligned_offsets_obj_spaced:
  "\<lbrakk> offsets_align kh (set (aligned_offsets p sz align)) align; is_aligned p sz \<rbrakk> \<Longrightarrow>
   obj_spaced kh (aligned_offsets p sz align)"
  apply (clarsimp simp: obj_spaced_nth offsets_align_def)
  apply (simp add: aligned_offsets_nth length_aligned_offsets ring_distribs add_ac)
  apply (erule (1) nth_aligned_offset_no_overflow)
  done

lemma set_aligned_offsets:
  "is_aligned p n \<Longrightarrow>
   set (aligned_offsets p sz n) = {p'. p \<le> p' \<and> p' \<le> p + mask sz} \<inter> {p. is_aligned p n}"
  apply (clarsimp simp: aligned_offsets_def upto_enum_step_def)
  apply (rule conjI)
   apply fastforce
  apply (clarsimp simp: not_less)
  apply (rule equalityI; clarsimp)
   apply (rule conjI; clarsimp)
    apply (meson div_to_mult_word_lt word_plus_mono_right word_plus_mono_right2)
   apply (erule is_aligned_add)
   apply (rule is_aligned_mult_triv2)
  apply (clarsimp simp: image_iff)
  apply (simp flip: shiftr_div_2n_w shiftl_eq_mult)
  apply (rule_tac x="(x - p) >> n" in exI)
  apply (rule conjI)
   apply (simp add: add.commute le_shiftr word_diff_ls')
  apply (prop_tac "is_aligned (x - p) n")
   apply (erule (1) aligned_sub_aligned_simple)
  apply (simp add: is_aligned_shiftr_shiftl)
  done

lemma aligned_offsets_neq_Nil:
  "is_aligned p sz \<Longrightarrow> aligned_offsets p sz n \<noteq> []"
  apply (prop_tac "length (aligned_offsets p sz n) \<noteq> 0")
   apply (simp add: length_aligned_offsets)
  apply clarsimp
  done

lemma hd_aligned_offsets:
  "\<lbrakk> is_aligned p sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow> hd (aligned_offsets p sz n) = p" for p::"'a::len word"
  apply (prop_tac "length (aligned_offsets p sz n) \<noteq> 0")
   apply (simp add: length_aligned_offsets)
  apply clarsimp
  apply (frule is_aligned_no_overflow_mask)
  apply (simp add: upto_enum_step_def not_less aligned_offsets_def split: if_splits)
  apply (rule conjI, fastforce)
  apply (simp add: hd_map)
  apply (simp flip: shiftr_div_2n_w shiftl_eq_mult add: shiftr_mask2)
  apply (clarsimp simp: upto_enum_def hd_append hd_map)
  apply (simp add: unat_eq_zero)
  done

lemma hd_aligned_offsets_append:
  "\<lbrakk> is_aligned p sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow> hd (aligned_offsets p sz n @ xs) = p"
  for p::"'a::len word"
  by (simp add: aligned_offsets_neq_Nil hd_aligned_offsets)

lemma obj_spaced_cons_aligned_offsets:
  "\<lbrakk> is_aligned p' sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow>
   obj_spaced kh (p # aligned_offsets p' sz n @ xs) =
   (p + mask (align_of kh p) < p' \<and> obj_spaced kh (aligned_offsets p' sz n @ xs))"
  for p::"'a::len word"
  apply (frule (1) hd_aligned_offsets[where n=n])
  apply (drule aligned_offsets_neq_Nil[where n=n])
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma last_aligned_offsets:
  "is_aligned p sz \<Longrightarrow> last (aligned_offsets p sz n) = p + (mask sz >> n << n)"
  apply (frule aligned_offsets_neq_Nil[where n=n])
  apply (simp add: last_conv_nth aligned_offsets_nth length_aligned_offsets)
  apply (simp flip: shiftr_div_2n_w shiftl_t2n')
  done

lemma last_aligned_offests_plus_mask:
  "\<lbrakk> offsets_align kh (set (aligned_offsets p sz n)) n; is_aligned p sz; n \<le> sz \<rbrakk> \<Longrightarrow>
   last (aligned_offsets p sz n) + mask (align_of kh (last (aligned_offsets p sz n))) =
   p + mask sz"
proof -
  assume sz: "n \<le> sz"
  assume [simp]: "is_aligned p sz"
  hence "aligned_offsets p sz n \<noteq> []"
    by (rule aligned_offsets_neq_Nil)
  moreover
  assume "offsets_align kh (set (aligned_offsets p sz n)) n"
  ultimately
  have [simp]: "align_of kh (last (aligned_offsets p sz n)) = n"
    by (simp add: offsets_align_def)
  have "last (aligned_offsets p sz n) = p + (mask sz >> n << n)"
    by (simp add: last_aligned_offsets)
  also
  have "... + mask n = p + (mask sz && ~~mask n) + mask n"
    by (simp add: and_not_mask)
  also
  from mask_and_neg_mask_compose[OF sz]
  have "...  = p + mask sz"
    by simp
  finally
  have "last (aligned_offsets p sz n) + mask n = p + mask sz" .
  thus ?thesis
    by simp
qed

end (* locale sorted_addrs *)

end