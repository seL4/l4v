(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ptr_auxupd
imports "CParser.CTranslation"
begin

definition
  "typ_clear_region ptr bits d \<equiv>
  \<lambda>x. (fst (d x), if x \<in> {ptr..+2 ^ bits} then Map.empty else (snd (d x)))"

declare [[calculate_modifies_proofs = false]]

external_file "ptr_auxupd.c"
install_C_file "ptr_auxupd.c"

(* FIXME: modifies proof fails, doesn't recognise AUXUPD *)
(* This is already present in the 2009-1 version *)

context ptr_auxupd begin

thm alloc_body_def

end

end
