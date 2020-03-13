(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ghoststate1
imports "CParser.CTranslation"
begin

external_file "simple_annotated_fn.c"
install_C_file "simple_annotated_fn.c" [ghostty="nat \<Rightarrow> nat"]

(* demonstrates existence of ghost'state global variable of appropriate type *)
term "\<acute>ghost'state :== (\<lambda>x. x + (1::nat))"

end
