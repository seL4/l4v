(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Deterministic_AC
imports
  "AInvs.AInvsToplevel_AI"
begin

(*This theory defines an abstract "integrity" property over
  the extensible specification that the deterministic specification
  is shown to preserve. Essentially it demonstrates that the only
  elements altered in the cdt_list are the given parameters and
  their descendants. *)

(* Analagous to the Control edges that pas_refined imposes. *)
definition all_children where
"all_children P m \<equiv> (\<forall>c p. m c = Some p \<longrightarrow> P p \<longrightarrow> P c)"

primrec list_filter :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list" where
  "list_filter [] P = []" |
  "list_filter (x # xs) P = (if (P x) then (list_filter xs P)
                             else x # (list_filter xs P))"

abbreviation
"filtered_eq P list list' \<equiv> list_filter list P = list_filter list' P"

lemma list_filter_distr[simp]: "list_filter (list @ list') P = (list_filter list P) @ (list_filter list' P)"
  apply (induct list,simp+)
  done

lemma list_filter_empty[simp]: "\<forall>x \<in> set list. P x \<Longrightarrow> list_filter list P = []"
  apply (induct list,simp+)
  done

lemma list_filter_replace_list: "\<forall>x \<in> set list'. P x \<Longrightarrow> P a \<Longrightarrow>
 filtered_eq P (list_replace_list list a list') list"
  apply (induct list,simp+)
  done

lemma list_filter_insert_after: "P b \<Longrightarrow>
 filtered_eq P (list_insert_after list a b) list"
  apply (induct list,simp+)
  done

lemma list_filter_swap: "P b \<Longrightarrow> P a \<Longrightarrow>
 filtered_eq P (list_swap list a b) list"
  apply (induct list,(simp add: list_swap_def)+)
  done

lemma list_filter_replace: "P b \<Longrightarrow> P a \<Longrightarrow>
 filtered_eq P (list_replace list a b) list"
  apply (induct list,(simp add: list_replace_def)+)
  done

lemma list_filter_remove: "P a \<Longrightarrow>
 filtered_eq P (list_remove list a) list"
  apply (induct list,simp+)
  done


(* Here P is meant to decide whether a cslot_ptr is part of the current
   subject. Integrity is said to hold of two cdt_lists if either an
   entry is part of the current subject, or their lists are equivalent
   with all entries from the current subject removed.

   We use this to reason that changes to a non-subject entry are only allowed
   if that entry's list contains a child that is part of the current subject.
   It is stated in this way so that the property can be shown to be transitive.*)

definition list_integ where
"list_integ P t t' \<equiv>  \<forall>x. P x \<or> (filtered_eq P (cdt_list t x) (cdt_list t' x))"

lemmas list_integI = list_integ_def[THEN meta_eq_to_obj_eq,THEN iffD2,rule_format]
lemma list_integE:
  assumes hyp: "list_integ P t t'"
  obtains "P x" | "(filtered_eq P (cdt_list t x) (cdt_list t' x))"
  using hyp list_integ_def by blast


lemma update_cdt_list_wp:
  "\<lbrace>(\<lambda>s. P (s\<lparr>cdt_list := f (cdt_list s)\<rparr>))\<rbrace> update_cdt_list f \<lbrace>\<lambda>_.P\<rbrace>"
  apply (simp add: update_cdt_list_def set_cdt_list_def)
  apply wp
  done


lemma cap_move_list_integrity:
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and K(P src) and K(P dest)\<rbrace> cap_move_ext src dest src_p dest_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: cap_move_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  apply (intro impI conjI allI | simp add: list_filter_replace list_filter_remove split: option.splits | elim conjE | simp add: list_integ_def)+
  done

lemma cap_insert_list_integrity:
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and K(P dest)\<rbrace> cap_insert_ext src_parent src dest src_p dest_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: cap_insert_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  by (intro impI conjI allI |
      simp add: list_filter_insert_after list_filter_remove split: option.splits |
      elim conjE | simp add: list_integ_def)+

lemma create_cap_list_integrity:
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and K(P dest)\<rbrace> create_cap_ext untyped dest dest_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: create_cap_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  by (intro impI conjI allI |
      simp add: list_filter_replace list_filter_remove split: option.splits |
      elim conjE | simp add: list_integ_def)+


lemma empty_slot_list_integrity:
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and (\<lambda>s. valid_list_2 (cdt_list s) m) and K(P slot) and K( all_children P m)\<rbrace> empty_slot_ext slot slot_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: empty_slot_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  apply (intro impI conjI allI | simp add: list_filter_replace_list list_filter_remove split: option.splits | elim conjE  | simp add: list_integ_def)+
  apply (drule_tac x="the slot_p" in spec)
  apply (elim disjE)
   apply (simp add: all_children_def valid_list_2_def list_filter_replace_list)+
  done


lemma cap_swap_list_integrity:
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and K(P slot1) and K(P slot2)\<rbrace> cap_swap_ext slot1 slot2 slot1_p slot2_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: cap_swap_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  by (intro impI conjI allI |
      simp add: list_filter_replace list_filter_swap split: option.splits |
      elim conjE | simp add: list_integ_def)+ (* slow *)

lemma null_filter: "\<forall>x \<in> set list. \<not> P x \<Longrightarrow> list_filter list P = list"
  apply (induct list,simp+)
  done

lemma neq_filtered_ex: "list \<noteq> list' \<Longrightarrow> filtered_eq P list list' \<Longrightarrow> \<exists>x \<in> set list \<union> set list'. P x"
  apply (rule ccontr)
  apply (simp add: null_filter)
  done

lemma weaken_filter: "(\<forall>s. P s \<longrightarrow> T s) \<Longrightarrow> filtered_eq T (list_filter list P) list"
  apply (induct list,simp+)
  done

lemmas weaken_filter' = weaken_filter[rule_format,rotated]

lemma weaken_filter_eq: "(\<forall>s. P s \<longrightarrow> T s) \<Longrightarrow> filtered_eq P list list' \<Longrightarrow> filtered_eq T list list'"
  apply (subst weaken_filter[symmetric],assumption)
  apply (simp add: weaken_filter)
  done

lemmas weaken_filter_eq' = weaken_filter_eq[rule_format,rotated]

end
