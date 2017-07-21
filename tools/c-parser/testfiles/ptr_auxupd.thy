(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ptr_auxupd
imports "../CTranslation"
begin

definition
  "typ_clear_region ptr bits d \<equiv>
  \<lambda>x. (fst (d x), if x \<in> {ptr..+2 ^ bits} then empty else (snd (d x)))"

declare [[calculate_modifies_proofs = false]]

install_C_file "ptr_auxupd.c"

(* FIXME: modifies proof fails, doesn't recognise AUXUPD *)
(* This is already present in the 2009-1 version *)

context ptr_auxupd begin

thm alloc_body_def

end

end
