(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WordAbsFnCall imports
  "AutoCorres.AutoCorres"
begin

external_file "word_abs_fn_call.c"
install_C_file "word_abs_fn_call.c"

(* Test interaction of abstracted/non-abstracted functions calling the
 * opposite. Also test interaction with heap abstraction. *)
autocorres [ unsigned_word_abs = bar bar2 bar5 bar6 foo3 foo4 foo7 foo8,
             no_heap_abs = foo3 foo4 foo7 foo8 ] "word_abs_fn_call.c"

end
