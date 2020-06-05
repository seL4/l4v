(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CommonOps
imports
  "CLib.CTranslationNICTA"
  GlobalsSwap
  ArchSetup
begin

text \<open>Additional constants needed to make conversion to and from the graph lang easy\<close>

definition
  bvshl :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvshl x y = x << (unat y)"

definition
  bvlshr :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvlshr x y = x >> (unat y)"

definition
  bvashr :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvashr x y = x >>> (unat y)"

definition
  bv_shift_amount :: "nat => 'a :: len word"
where
 "bv_shift_amount n = of_nat (min n ((2 ^ len_of TYPE('a)) - 1))"

definition
  bv_clz :: "('a :: len) word \<Rightarrow> 'a word"
where
  "bv_clz x = of_nat (word_clz x)"

definition
  bv_ctz :: "('a :: len) word \<Rightarrow> 'a word"
where
  "bv_ctz x = of_nat (word_ctz x)"

definition
  bv_popcount :: "('a :: len) word \<Rightarrow> 'a word"
where
  "bv_popcount x = of_nat (pop_count x)"

definition
  "mem_acc mem addr = h_val mem (Ptr addr)"

definition
  "mem_upd mem addr v = heap_update (Ptr addr) v mem"

definition
  "store_word8 (addr :: addr) (w :: word8) m = m (addr := w)"

definition
  "load_word8 (addr :: addr) m = (m addr :: word8)"

definition
  "store_word32 (addr :: addr) (w :: word32)
    = heap_update_list addr (rev (word_rsplit w))"

definition
  "load_word32 (addr :: addr) memory
    = (word_rcat (rev (heap_list memory 4 addr)) :: word32)"

definition
  "store_word64 (addr :: addr) (w :: word64)
    = heap_update_list addr (rev (word_rsplit w))"

definition
  "load_word64 (addr :: addr) memory
    = (word_rcat (rev (heap_list memory 8 addr)) :: word64)"

abbreviation (input)
  "store_machine_word :: machine_word mem_upd
    \<equiv> arch_store_machine_word store_word32 store_word64"

abbreviation (input)
  "load_machine_word :: machine_word mem_read
    \<equiv> arch_load_machine_word load_word32 load_word64"

definition
  word_add_with_carry :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> bool
    \<Rightarrow> ('a word \<times> (bool \<times> bool))"
where
 "word_add_with_carry x y cin \<equiv>
  let cinw = if cin then 1 else 0
  in (x + y + cinw,
      unat (x + y + cinw) \<noteq> unat x + unat y + unat cinw,
      (msb x \<noteq> msb y) \<and> (msb x \<noteq> msb (x + y + cinw)))"

\<comment> \<open>
  `all_htd_updates` is a utility term that we use to stash HTD updates when
  going into and out of GraphLang.
\<close>
definition
  all_htd_updates :: "('a :: c_type) itself \<Rightarrow> machine_word \<Rightarrow> addr \<Rightarrow> machine_word
        \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "all_htd_updates (tp :: ('a :: c_type) itself) mode p sz
    = (if mode = 0
        then typ_clear_region p (unat sz)
        else if mode = 1 then ptr_retyps (unat sz) (Ptr p:: 'a ptr)
        else if mode = 2 then typ_region_bytes p (unat sz)
        else if mode = 3 then ptr_retyps (2 ^ unat sz) (Ptr p :: 'a ptr)
        else if mode = 4 then ptr_arr_retyps (unat sz) (Ptr p :: 'a ptr)
        else ptr_arr_retyps (2 ^ unat sz) (Ptr p :: 'a ptr))"

\<comment> \<open>
  This type has a weird domain @{typ "50 word"} to help you figure out the
  source of your problem when asmrefine breaks - if you see `50 word`, it's
  probably a ghost_assertions problem.
\<close>
type_synonym ghost_assertions = "50 word \<Rightarrow> addr"

definition
  ghost_assertion_data_get :: "int \<Rightarrow> ('a \<Rightarrow> ghost_assertions) \<Rightarrow> 'a \<Rightarrow> addr"
where
  "ghost_assertion_data_get k acc s = (acc s) (word_of_int k)"

definition
  ghost_assertion_data_set :: "int \<Rightarrow> addr \<Rightarrow> ((ghost_assertions \<Rightarrow> ghost_assertions) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "ghost_assertion_data_set k v upd = upd (\<lambda>f. f (word_of_int k := v))"

definition
  "pvalid htd (v :: ('a :: c_type) itself) x = h_t_valid htd c_guard (Ptr x :: 'a ptr)"

definition
  "palign_valid (v :: ('a :: c_type) itself) x = c_guard (Ptr x :: 'a ptr)"

definition
  "pweak_valid htd (v :: ('a :: c_type) itself) x = ptr_safe (Ptr x :: 'a ptr) htd"

definition
  "pglobal_valid htd (v :: ('a :: mem_type) itself) x = ptr_inverse_safe (Ptr x :: 'a ptr) htd"

definition
  "parray_valid htd (v :: ('a :: c_type) itself) x n
    = array_assertion (Ptr x :: 'a ptr) (unat n) htd"

end

