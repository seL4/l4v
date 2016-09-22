(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordAbsFnCall imports
  "../../AutoCorres"
begin

install_C_file "word_abs_fn_call.c"

(* Test interaction of abstracted/non-abstracted functions calling the
 * opposite. Also test interaction with heap abstraction. *)
autocorres [ unsigned_word_abs = bar bar2 bar5 bar6 foo3 foo4 foo7 foo8,
             no_heap_abs = foo3 foo4 foo7 foo8 ] "word_abs_fn_call.c"

end
