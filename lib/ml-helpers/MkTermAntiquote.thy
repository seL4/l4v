(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

text \<open>
  mk_term: ML antiquotation for building and splicing terms.

  See MkTermAntiquote_Tests for examples and tests.
\<close>
theory MkTermAntiquote
imports
  Pure
begin

(* Simple wrapper theory for historical reasons. *)
ML_file "mkterm_antiquote.ML"

end