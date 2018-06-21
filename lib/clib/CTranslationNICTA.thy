(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CTranslationNICTA
imports
  "CParser.CTranslation"
  "Word_Lib.Word_Lib"
begin

declare len_of_numeral_defs [simp del]

definition
  "typ_clear_region ptr bits d \<equiv> \<lambda>x. (fst (d x), if x \<in> {ptr..+2 ^ bits} then Map.empty else (snd (d x)))"

definition
  "typ_region_bytes ptr bits d \<equiv> \<lambda>x. (if x \<in> {ptr ..+ 2 ^ bits}
     then (True, [0 \<mapsto> (typ_uinfo_t TYPE(word8), True)]) else d x)"

fun
  ptr_retyps :: "nat \<Rightarrow> 'a :: c_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "ptr_retyps 0 p d = d"
| "ptr_retyps (Suc n) p d = ptr_retyp p (ptr_retyps n (CTypesDefs.ptr_add p 1) d)"

end
