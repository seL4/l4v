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
 * opposite. *)
autocorres [unsigned_word_abs = bar bar2 foo3 foo4 ] "word_abs_fn_call.c"

end
