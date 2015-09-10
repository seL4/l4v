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

theory HeapRawState
imports CTypes
begin

type_synonym typ_base = bool
datatype s_heap_index = SIndexVal | SIndexTyp nat
datatype s_heap_value = SValue byte | STyp "typ_uinfo \<times> typ_base"

primrec (nonexhaustive)
  s_heap_tag :: "s_heap_value \<Rightarrow> typ_uinfo \<times> typ_base"
where
  "s_heap_tag (STyp t) = t"

type_synonym typ_slice = "nat \<rightharpoonup> typ_uinfo \<times> typ_base"
(*  heap_typ_desc = "addr \<Rightarrow> tag_ladder"*)
type_synonym s_addr = "addr \<times> s_heap_index"
type_synonym heap_state = "s_addr \<rightharpoonup> s_heap_value"
type_synonym heap_typ_desc = "addr \<Rightarrow> bool \<times> typ_slice"
type_synonym heap_raw_state = "heap_mem \<times> heap_typ_desc"

(* Used in the C parser to avoid loss of information about the relative
   ordering of heap_updates and ptr_tags, as this order conveys the intention
   of the type of a memory location that can be helpful when reducing over
   multiple updates of both the heap memory state and heap type description
*)

definition hrs_mem :: "heap_raw_state \<Rightarrow> heap_mem" where
  "hrs_mem \<equiv> fst"

definition
  hrs_mem_update :: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> heap_raw_state \<Rightarrow> heap_raw_state"
where
  "hrs_mem_update f \<equiv> \<lambda>(h,d). (f h,d)"

definition hrs_htd :: "heap_raw_state \<Rightarrow> heap_typ_desc" where
  "hrs_htd \<equiv> snd"

definition
  hrs_htd_update :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> heap_raw_state
                     \<Rightarrow> heap_raw_state"
where
  "hrs_htd_update f \<equiv> \<lambda>(h,d). (h,f d)"


lemma hrs_comm:
  "hrs_htd_update d (hrs_mem_update h s) = hrs_mem_update h (hrs_htd_update d s)"
  by (simp add: hrs_htd_update_def hrs_mem_update_def split_def)

lemma hrs_htd_update_htd_update:
  "(\<lambda>s. hrs_htd_update d (hrs_htd_update d' s)) = hrs_htd_update (d \<circ> d')"
  by (simp add: hrs_htd_update_def split_def)


lemma hrs_htd_mem_update [simp]:
  "hrs_htd (hrs_mem_update f s) = hrs_htd s"
  by (simp add: hrs_mem_update_def hrs_htd_def split_def)

lemma hrs_mem_htd_update [simp]:
  "hrs_mem (hrs_htd_update f s) = hrs_mem s"
  by (simp add: hrs_htd_update_def hrs_mem_def split_def)

lemma hrs_mem_update:
  "hrs_mem (hrs_mem_update f s) = (f (hrs_mem s))"
  by (simp add: hrs_mem_update_def hrs_mem_def split_def)

lemma hrs_htd_update:
  "hrs_htd (hrs_htd_update f s) = (f (hrs_htd s))"
  by (simp add: hrs_htd_update_def hrs_htd_def split_def)

lemmas hrs_update = hrs_mem_update hrs_htd_update


end
