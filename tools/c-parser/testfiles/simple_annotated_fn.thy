(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple_annotated_fn
imports "CParser.CTranslation"
begin

consts
  FACT :: "32 word \<Rightarrow> 32 word"

(* defining an appropriate FACT is left as an exercise for the reader
primrec
  "FACT 0 = 1"
  "FACT (Suc n) = Suc n * FACT n"
*)

external_file "simple_annotated_fn.c"
install_C_file "simple_annotated_fn.c"

print_locale simple_annotated_fn_global_addresses
thm simple_annotated_fn_global_addresses.fact_body_def
thm simple_annotated_fn_global_addresses.fact_impl

end
