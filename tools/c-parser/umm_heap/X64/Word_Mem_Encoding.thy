(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Word_Mem_Encoding
  imports Vanilla32_Preliminaries
begin

(* Little-endian encoding *)
definition
  word_tag :: "'a::len8 word itself \<Rightarrow> 'a word typ_info"
where
  "word_tag (w::'a::len8 word itself) \<equiv>
    TypDesc (TypScalar (len_of TYPE('a) div 8)
                       (len_exp TYPE('a))
                       \<lparr> field_access = \<lambda>v bs. (rev o word_rsplit) v,
                         field_update = \<lambda>bs v. (word_rcat (rev bs)::'a::len8 word) \<rparr>)
            (signed_or_unsigned_as_str TYPE('a) @ ''word'' nat_to_bin_string (len_of TYPE('a)))"

end
