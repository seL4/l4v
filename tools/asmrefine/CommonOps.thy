(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CommonOps

imports "../../lib/CTranslationNICTA"
  "GlobalsSwap"

begin

text {* Additional constants needed to make conversion to graph lang easy *}

definition
  bvshl :: "'a :: len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvshl x y = x << (unat y)"

definition
  bvlshr :: "'a :: len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
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
  "count_leading_zeroes z = length (takeWhile Not (to_bl z))"

definition
  "count_trailing_zeroes z = length (takeWhile Not (rev (to_bl z)))"

definition
  bv_clz :: "('a :: len) word \<Rightarrow> 'a word"
where
  "bv_clz x = of_nat (count_leading_zeroes x)"

definition
  "mem_acc mem addr = h_val mem (Ptr addr)"

definition
  "mem_upd mem addr v = heap_update (Ptr addr) v mem"

definition
 "store_word32 (addr :: word32) (w :: word32)
    = heap_update_list addr (rev (word_rsplit w))"

definition
 "load_word32 (addr :: word32) memory
    = (word_rcat (rev (heap_list memory 4 addr)) :: word32)"

definition
 "store_word8 (addr :: word32) (w :: word8) m = m (addr := w)"

definition
 "load_word8 (addr :: word32) m = (m addr :: word8)"

definition
  word_add_with_carry :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> bool
    \<Rightarrow> ('a word \<times> (bool \<times> bool))"
where
 "word_add_with_carry x y cin \<equiv>
  let cinw = if cin then 1 else 0
  in (x + y + cinw,
      unat (x + y + cinw) \<noteq> unat x + unat y + unat cinw,
      (msb x \<noteq> msb y) \<and> (msb x \<noteq> msb (x + y + cinw)))"

definition
  all_htd_updates :: "('a :: c_type) itself \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32
        \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "all_htd_updates (tp :: ('a :: c_type) itself) x y z
    = (if x = 0
        then typ_clear_region y (unat z)
        else if x = 1 then ptr_retyps (unat z) (Ptr y :: 'a ptr)
        else if x = 2 then typ_region_bytes y (unat z)
        else if x = 3 then ptr_retyps (2 ^ unat z) (Ptr y :: 'a ptr)
        else if x = 4 then ptr_arr_retyps (unat z) (Ptr y :: 'a ptr)
        else ptr_arr_retyps (2 ^ unat z) (Ptr y :: 'a ptr))"

type_synonym ghost_assertions = "word64 \<Rightarrow> word32"

definition
  ghost_assertion_data_get :: "int \<Rightarrow> ('a \<Rightarrow> ghost_assertions) \<Rightarrow> 'a \<Rightarrow> word32"
where
  "ghost_assertion_data_get k acc s = (acc s) (word_of_int k)"

definition
  ghost_assertion_data_set :: "int \<Rightarrow> word32 \<Rightarrow> ((ghost_assertions \<Rightarrow> ghost_assertions) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
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

